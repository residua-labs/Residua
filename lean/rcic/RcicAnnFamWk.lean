import rcic.RcicAnnFam
import rcic.RcicAnnSynMap
import rcic.RcicAnnTyRedWk

/-!
# M2-f (3) — the `fam` clause's ingredients weaken

Along a whole weakening spec `σ` (`wkExprA σ`, a shape map — `wkMapA`): typed term
chains (`tyHRedA_wk`, `tmChainA_wk`, `tyHRedStarA_wk`), constructor heads and stuck
terms (`ctorHeadA_wk`, `stuckTmA_wk`), the argument walks (`argsRelPA_wk`,
`argsRelA_wk`: given weakening of the position relations at doubly-related prefixes
— what the relation's induction hypothesis and the kill criterion supply) and the
fixed point itself (`lfpWA_wk`, from the clause's own world to the extension; L-RING C6's
`lfp_wk` on the copy) and its reindexing along a weakened clause (`lfpWA_reindex`). Member types are
closed (`EnvClosedA`), so a telescope read off a member is fixed by the spec and only
the arguments move (`applyTelA_wk_closed`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section FamWk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- parameter conversions weaken along a spec (M2-f (6)). -/
theorem convArgsA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) : ∀ {T : ExprA} {xs ys : List ExprA}, ConvArgsA E I n Γ T xs ys →
      ConvArgsA E I n (wkCtxA σ Γ) (wkExprA σ T) (xs.map (wkExprA σ)) (ys.map (wkExprA σ))
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A u B v f f' fs fs' hc hs => by
      rw [wkExprA_pi_ub, List.map_cons, List.map_cons]
      refine .cons _ u _ v _ _ _ _ (convA_wk_ne hE hI σ hσ hc) ?_
      rw [← wkExprA_instantiate0A]
      exact convArgsA_wk hE hI σ hσ hs

theorem parConvA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) : ∀ {T T' : ExprA} {xs ys : List ExprA}, ParConvA E I n Γ T T' xs ys →
      ParConvA E I n (wkCtxA σ Γ) (wkExprA σ T) (wkExprA σ T') (xs.map (wkExprA σ)) (ys.map (wkExprA σ))
  | _, _, _, _, .nil _ _ => .nil _ _
  | _, _, _, _, .cons A u B v A' u' B' v' f f' fs fs' hc hd hs => by
      rw [wkExprA_pi_ub, wkExprA_pi_ub, List.map_cons, List.map_cons]
      refine .cons _ u _ v _ u' _ v' _ _ _ _ (convA_wk_ne hE hI σ hσ hc) (tyConvA_wk_ne hE hI σ hσ hd) ?_
      rw [← wkExprA_instantiate0A, ← wkExprA_instantiate0A]
      exact parConvA_wk hE hI σ hσ hs

def tmChainA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) {A : ExprA} : {a N : ExprA} → TmChainA E I n Γ A a N →
    TmChainA E I n (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ a) (wkExprA σ N)
  | _, _, .refl a h => .refl _ (hasTyA_wk hE hI Γ σ hσ h)
  | _, _, .cons a _ N ha hs t =>
      .cons _ _ _ (hasTyA_wk hE hI Γ σ hσ ha) (tyHRedA_wk hE hI Γ σ hσ hs) (tmChainA_wk hE hI σ hσ t)

theorem tyHRedStarA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) {a N A : ExprA} (h : TyHRedStarA E I n Γ a N A) :
    TyHRedStarA E I n (wkCtxA σ Γ) (wkExprA σ a) (wkExprA σ N) (wkExprA σ A) :=
  h.elim fun t => ⟨tmChainA_wk hE hI σ hσ t⟩

/-- a weakened term is a constant only if the term is. -/
theorem wkExprA_eq_const (σ : WkSpecA) : (e : ExprA) → {c : Nat} → {ls : List Level} →
    wkExprA σ e = .const c ls → e = .const c ls
  | .const _ _, _, _, h => by rw [wkExprA_const] at h; exact h
  | .bvar _, _, _, h => by rw [wkExprA_bvar_idx] at h; exact ExprA.noConfusion h
  | .sort _, _, _, h => by rw [wkExprA_sort] at h; exact ExprA.noConfusion h
  | .app _ _, _, _, h => by rw [wkExprA_app] at h; exact ExprA.noConfusion h
  | .lam _ _ _, _, _, h => by rw [wkExprA_lam_ub] at h; exact ExprA.noConfusion h
  | .pi _ _ _ _, _, _, h => by rw [wkExprA_pi_ub] at h; exact ExprA.noConfusion h
  | .letE _ _ _, _, _, h => by rw [wkExprA_letE_ub] at h; exact ExprA.noConfusion h
  | .lit _, _, _, h => by rw [wkExprA_lit] at h; exact ExprA.noConfusion h

theorem ctorHeadA_wk (σ : WkSpecA) {N : ExprA} (h : CtorHeadA E N) : CtorHeadA E (wkExprA σ N) := by
  obtain ⟨c, ls, m, hh, hm, hk⟩ := h
  refine ⟨c, ls, m, ?_, hm, hk⟩
  simp only [appsSpineA_wkExprA, hh, wkExprA_const]

theorem ctorHeadA_wk_rev (σ : WkSpecA) {N : ExprA} (h : CtorHeadA E (wkExprA σ N)) : CtorHeadA E N := by
  obtain ⟨c, ls, m, hh, hm, hk⟩ := h
  rw [appsSpineA_wkExprA] at hh
  exact ⟨c, ls, m, wkExprA_eq_const σ _ hh, hm, hk⟩

theorem stuckTmA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) {N : ExprA} (h : StuckTmA E I Γ N) :
    StuckTmA E I (wkCtxA σ Γ) (wkExprA σ N) :=
  ⟨hStepFnA_wk_none hE hI Γ σ hσ h.1, fun hc => h.2 (ctorHeadA_wk_rev σ hc)⟩

theorem wkOk₀A_comp {Γ : LCtxA} {σ ρ : WkSpecA} (hσ : WkOkA E I n σ Γ)
    (hρ : WkOk₀A E I n ρ (wkCtxA σ Γ)) : WkOk₀A E I n (WkSpecA.comp σ ρ) Γ := by
  rcases hρ with rfl | hρ
  · rw [WkSpecA.comp_nil]; exact Or.inr hσ
  · exact Or.inr (wkOkA_comp hσ hρ)

/-! ## the walks weaken -/

/-- a telescope applied to weakened arguments, weakened (any telescope: `wkMapA` is a
    shape map). -/
theorem applyTelA_wk (σ : WkSpecA) (xs : List ExprA) (T : ExprA) :
    applyTelA (xs.map (wkExprA σ)) (wkExprA σ T) = (applyTelA xs T).map (wkExprA σ) :=
  (wkMapA σ).applyTelA_shape xs T

theorem carrierParamsA_wk (σ : WkSpecA) (m : CheckedMemberA) (A : ExprA) :
    carrierParamsA m (wkExprA σ A) = (carrierParamsA m A).map (wkExprA σ) := by
  simp only [carrierParamsA, appsSpineA_wkExprA, List.map_take]

theorem carrierLevelsA_wk (σ : WkSpecA) (A : ExprA) :
    carrierLevelsA (wkExprA σ A) = carrierLevelsA A := by
  simp only [carrierLevelsA, appsSpineA_wkExprA]
  generalize (appsSpineA A).1 = h
  cases h <;> simp [wkExprA_const, wkExprA_bvar_idx, wkExprA_sort, wkExprA_app, wkExprA_lam_ub,
    wkExprA_pi_ub, wkExprA_letE_ub, wkExprA_lit]

/-- the plain walk weakens, from any start `(i₀, prev₀, T₀)`, given weakening of the
    position relations at related prefixes (what the relation's induction hypothesis
    and `TyKA_unique` supply). -/
theorem argsRelPA_wk {R R' : Nat → List ExprA → ExprA → ExprA → Prop} (σ : WkSpecA) {i₀ : Nat}
    {prev₀ : List ExprA} {T₀ : ExprA}
    (hcomp : ∀ (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (f f' : ExprA),
      ArgsRelPA R i₀ prev₀ T₀ pre pre' →
      ArgsRelPA R' i₀ (prev₀.map (wkExprA σ)) (wkExprA σ T₀) (pre.map (wkExprA σ)) (pre'.map (wkExprA σ)) →
      applyTelA pre T₀ = some (.pi D uD C vC) → R (i₀ + pre.length) (prev₀ ++ pre) f f' →
      R' (i₀ + pre.length) ((prev₀ ++ pre).map (wkExprA σ)) (wkExprA σ f) (wkExprA σ f')) :
    ∀ {i : Nat} {prev pre pre' : List ExprA} {T : ExprA} {xs xs' : List ExprA},
      ArgsRelPA R i prev T xs xs' → i = i₀ + pre.length → prev = prev₀ ++ pre →
      applyTelA pre T₀ = some T →
      ArgsRelPA R i₀ prev₀ T₀ pre pre' →
      ArgsRelPA R' i₀ (prev₀.map (wkExprA σ)) (wkExprA σ T₀) (pre.map (wkExprA σ)) (pre'.map (wkExprA σ)) →
      ArgsRelPA R' i (prev.map (wkExprA σ)) (wkExprA σ T) (xs.map (wkExprA σ)) (xs'.map (wkExprA σ)) := by
  intro i prev pre pre' T xs xs' h
  induction h generalizing pre pre' with
  | nil i prev T => intro _ _ _ _ _; exact .nil _ _ _
  | cons i prev A u B v f f' fs fs' hf _ ih =>
      intro hi hprev hT hp hp'
      subst hi; subst hprev
      have hf' := hcomp pre pre' A u B v f f' hp hp' hT hf
      have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ T₀) =
          some (.pi (wkExprA σ A) u (wkExprA (WkSpecA.ub σ) B) v) := by
        rw [applyTelA_wk σ pre T₀, hT]
        show some (wkExprA σ (.pi A u B v)) = _
        rw [wkExprA_pi_ub]
      have hp2 := argsRelPA_snoc hp (f := f) (f' := f') hT hf
      have hp2' := argsRelPA_snoc hp' (f := wkExprA σ f) (f' := wkExprA σ f') hTw
        (by simpa using hf')
      have ihr := ih (pre := pre ++ [f]) (pre' := pre' ++ [f']) (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) hp2 (by simpa using hp2')
      rw [wkExprA_pi_ub]
      refine .cons (i₀ + pre.length) ((prev₀ ++ pre).map (wkExprA σ)) (wkExprA σ A) u
        (wkExprA (WkSpecA.ub σ) B) v (wkExprA σ f) (wkExprA σ f') (fs.map (wkExprA σ))
        (fs'.map (wkExprA σ)) hf' ?_
      rw [← wkExprA_instantiate0A]
      simpa using ihr

/-- the constructor walk weakens, from any start: plain positions as above, recursive
    positions by the given closure of the fixed-point variable. -/
theorem argsRelA_wk {R R' : Nat → List ExprA → ExprA → ExprA → Prop} {X X' : CRelA}
    {F F' : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (σ : WkSpecA) {i₀ : Nat} {prev₀ : List ExprA} {T₀ : ExprA} (kinds : List FieldShape)
    (hX : ∀ A f f', X A f f' → X' (wkExprA σ A) (wkExprA σ f) (wkExprA σ f'))
    (hF : ∀ i prev A j f f', F i prev A j f f' →
      F' i (prev.map (wkExprA σ)) (wkExprA σ A) j (wkExprA σ f) (wkExprA σ f'))
    (hcomp : ∀ (ksPre ks : List FieldShape) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA)
      (vC : Level) (f f' : ExprA), kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre' →
      ArgsRelA R' X' F' i₀ (prev₀.map (wkExprA σ)) (wkExprA σ T₀) ksPre (pre.map (wkExprA σ))
        (pre'.map (wkExprA σ)) →
      applyTelA pre T₀ = some (.pi D uD C vC) → R (i₀ + ksPre.length) (prev₀ ++ pre) f f' →
      R' (i₀ + ksPre.length) ((prev₀ ++ pre).map (wkExprA σ)) (wkExprA σ f) (wkExprA σ f')) :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {ks : List FieldShape} {fs fs' : List ExprA},
      ArgsRelA R X F i prev T ks fs fs' →
      ∀ (ksPre : List FieldShape) (pre pre' : List ExprA),
        kinds = ksPre ++ ks → i = i₀ + ksPre.length → prev = prev₀ ++ pre → applyTelA pre T₀ = some T →
        ArgsRelA R X F i₀ prev₀ T₀ ksPre pre pre' →
        ArgsRelA R' X' F' i₀ (prev₀.map (wkExprA σ)) (wkExprA σ T₀) ksPre (pre.map (wkExprA σ))
          (pre'.map (wkExprA σ)) →
        ArgsRelA R' X' F' i (prev.map (wkExprA σ)) (wkExprA σ T) ks (fs.map (wkExprA σ))
          (fs'.map (wkExprA σ)) := by
  intro i prev T ks fs fs' h
  induction h with
  | nil i prev T => intro _ _ _ _ _ _ _ _ _; exact .nil _ _ _
  | plain i prev A u B v f f' ks fs fs' hR _ ih =>
      intro ksPre pre pre' hk hi hprev hT hp hp'
      subst hi; subst hprev
      have hR' := hcomp ksPre ks pre pre' A u B v f f' hk hp hp' hT hR
      have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ T₀) =
          some (.pi (wkExprA σ A) u (wkExprA (WkSpecA.ub σ) B) v) := by
        rw [applyTelA_wk σ pre T₀, hT]
        show some (wkExprA σ (.pi A u B v)) = _
        rw [wkExprA_pi_ub]
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') FieldShape.nonrecursive hT
        (by simp only [kindRelA]; exact hR)
      have hp2' := argsRelA_snoc hp' (f := wkExprA σ f) (f' := wkExprA σ f') FieldShape.nonrecursive hTw
        (by simp only [kindRelA]; simpa using hR')
      have ihr := ih (ksPre ++ [FieldShape.nonrecursive]) (pre ++ [f]) (pre' ++ [f'])
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) hp2 (by simpa using hp2')
      rw [wkExprA_pi_ub]
      refine .plain (i₀ + ksPre.length) ((prev₀ ++ pre).map (wkExprA σ)) (wkExprA σ A) u
        (wkExprA (WkSpecA.ub σ) B) v (wkExprA σ f) (wkExprA σ f') ks (fs.map (wkExprA σ))
        (fs'.map (wkExprA σ)) hR' ?_
      rw [← wkExprA_instantiate0A]
      simpa using ihr
  | directRec i prev A u B v f f' ks fs fs' hY _ ih =>
      intro ksPre pre pre' hk hi hprev hT hp hp'
      subst hi; subst hprev
      have hY' := hX A f f' hY
      have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ T₀) =
          some (.pi (wkExprA σ A) u (wkExprA (WkSpecA.ub σ) B) v) := by
        rw [applyTelA_wk σ pre T₀, hT]
        show some (wkExprA σ (.pi A u B v)) = _
        rw [wkExprA_pi_ub]
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') (FieldShape.recursive 0) hT hY
      have hp2' := argsRelA_snoc hp' (f := wkExprA σ f) (f' := wkExprA σ f') (FieldShape.recursive 0) hTw hY'
      have ihr := ih (ksPre ++ [(FieldShape.recursive 0)]) (pre ++ [f]) (pre' ++ [f'])
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) hp2 (by simpa using hp2')
      rw [wkExprA_pi_ub]
      refine .directRec (i₀ + ksPre.length) ((prev₀ ++ pre).map (wkExprA σ)) (wkExprA σ A) u
        (wkExprA (WkSpecA.ub σ) B) v (wkExprA σ f) (wkExprA σ f') ks (fs.map (wkExprA σ))
        (fs'.map (wkExprA σ)) hY' ?_
      rw [← wkExprA_instantiate0A]
      simpa using ihr
  | funRec i prev A u B v f f' j ks fs fs' hY _ ih =>
      intro ksPre pre pre' hk hi hprev hT hp hp'
      subst hi; subst hprev
      have hY' := hF _ _ A j f f' hY
      have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ T₀) =
          some (.pi (wkExprA σ A) u (wkExprA (WkSpecA.ub σ) B) v) := by
        rw [applyTelA_wk σ pre T₀, hT]
        show some (wkExprA σ (.pi A u B v)) = _
        rw [wkExprA_pi_ub]
      have hp2 := argsRelA_snoc hp (f := f) (f' := f') (FieldShape.recursive (j + 1)) hT
        (by simp only [kindRelA]; exact hY)
      have hp2' := argsRelA_snoc hp' (f := wkExprA σ f) (f' := wkExprA σ f') (FieldShape.recursive (j + 1)) hTw
        (by simp only [kindRelA]; simpa using hY')
      have ihr := ih (ksPre ++ [FieldShape.recursive (j + 1)]) (pre ++ [f]) (pre' ++ [f'])
        (by rw [hk, List.append_assoc]; rfl) (by simp; omega) (by simp)
        (applyTelA_snoc pre T₀ hT) hp2 (by simpa using hp2')
      rw [wkExprA_pi_ub]
      refine .funRec (i₀ + ksPre.length) ((prev₀ ++ pre).map (wkExprA σ)) (wkExprA σ A) u
        (wkExprA (WkSpecA.ub σ) B) v (wkExprA σ f) (wkExprA σ f') j ks (fs.map (wkExprA σ))
        (fs'.map (wkExprA σ)) hY' ?_
      rw [← wkExprA_instantiate0A]
      simpa using ihr

/-! ## the fixed point weakens (R-NoFunRec-1 step 1 (1a): from the clause's own world to `σ`) -/

/-- the declared pair weakens along a well-formed spec. -/
theorem declPairA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {σ : WkSpecA}
    (hσ : WkOkA E I n σ Γ) {A f f' : ExprA} (h : DeclPairA E I n Γ A f f') :
    DeclPairA E I n (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ f) (wkExprA σ f') :=
  ⟨hasTyA_wk_ne hE hI σ hσ.1 h.1, hasTyA_wk_ne hE hI σ hσ.1 h.2.1, convA_wk_ne hE hI σ hσ.1 h.2.2⟩

/-- the fixed point weakens ON A FIBER (carriers with parameters `ps`, levels `=ₙ ls₀`) from the
    clause's own world `[]` to a world `σ`, given weakening of the clause relations from the one
    world to the other at related prefixes (constructor fields along the telescopes at `ps`,
    family indices likewise). The fixed point at every world is carried beside the weakened one,
    so a position read at another world finds it there. -/
theorem lfpWA_wk (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I) {Γ : LCtxA}
    {σ : WkSpecA}
    (hσ : WkOkA E I n σ Γ) {r : Nat} {m : CheckedMemberA} (hm : E.members r = some m)
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA}
    {ps : List ExprA} {ls₀ : List Level}
    (hcomp : ∀ (c : Nat) (cm : CheckedMemberA) (lsC lsA : List Level) (kinds ksPre ks : List FieldShape)
      (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (f f' : ExprA),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls₀ lsA → eqNListB n lsA lsC →
      applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (Rs [] c lsC) (famRecRelA m ps lsA (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) []))
        (famFunRelA E I n (wkCtxA [] Γ) m (innerRelsA RsI [] c lsC) ps lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp [] ρ')))
        m.nparamsA ps T ksPre pre pre' →
      ArgsRelA (Rs σ c lsC) (famRecRelA m (ps.map (wkExprA σ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) σ))
        (famFunRelA E I n (wkCtxA σ Γ) m (innerRelsA RsI σ c lsC) (ps.map (wkExprA σ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp σ ρ')))
        m.nparamsA (ps.map (wkExprA σ)) (wkExprA σ T) ksPre (pre.map (wkExprA σ)) (pre'.map (wkExprA σ)) →
      applyTelA pre T = some (.pi D uD C vC) →
      Rs [] c lsC (m.nparamsA + ksPre.length) (ps ++ pre) f f' →
      Rs σ c lsC (m.nparamsA + ksPre.length) ((ps ++ pre).map (wkExprA σ)) (wkExprA σ f) (wkExprA σ f'))
    (hcompF : ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
      (C : ExprA) (vC : Level) (f f' : ExprA), eqNListB n ls₀ lsF →
      applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
      ArgsRelPA (RsF [] lsF) m.nparamsA ps TF pre pre' →
      ArgsRelPA (RsF σ lsF) m.nparamsA (ps.map (wkExprA σ)) (wkExprA σ TF) (pre.map (wkExprA σ))
        (pre'.map (wkExprA σ)) →
      applyTelA pre TF = some (.pi D uD C vC) →
      RsF [] lsF (m.nparamsA + pre.length) (ps ++ pre) f f' →
      RsF σ lsF (m.nparamsA + pre.length) ((ps ++ pre).map (wkExprA σ)) (wkExprA σ f) (wkExprA σ f')) :
    ∀ {A a b : ExprA}, carrierParamsA m A = ps → eqNList ls₀ (carrierLevelsA A) →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] A a b →
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) σ (wkExprA σ A) (wkExprA σ a) (wkExprA σ b) := by
  intro A a b hAp hAl h
  have hY := h (fun ρ C a b => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ C a b ∧
      (ρ = [] → carrierParamsA m C = ps → eqNList ls₀ (carrierLevelsA C) →
        LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) σ (wkExprA σ C) (wkExprA σ a) (wkExprA σ b)))
    (fun ρ C a b hs => by
      refine ⟨LfpWA.fold famPhiWA_mono (famPhiA_mono (fun _ _ _ h => h.1) (fun _ _ _ _ _ h => h.1) hs), ?_⟩
      intro hρ hCp hCl
      subst hρ
      have hX : ∀ D x y, famRecRelA m ps (carrierLevelsA C) (fun C a b =>
            LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] C a b ∧
            (([] : WkSpecA) = [] → carrierParamsA m C = ps → eqNList ls₀ (carrierLevelsA C) →
              LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) σ (wkExprA σ C) (wkExprA σ a) (wkExprA σ b))) D x y →
          famRecRelA m ps (carrierLevelsA C) (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) []) D x y ∧
          famRecRelA m (ps.map (wkExprA σ)) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) σ) (wkExprA σ D) (wkExprA σ x) (wkExprA σ y) :=
        fun D x y hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2.2 rfl hd.1 hlD
          refine ⟨⟨hd.1, hd.2.1, hd.2.2.1⟩, ⟨?_, ?_, hh⟩⟩
          · rw [carrierParamsA_wk, hd.1]
          · rw [carrierLevelsA_wk]; exact hd.2.1
      obtain ⟨hc, hs⟩ := hs
      refine LfpWA.fold famPhiWA_mono ⟨convA_wk_ne hE hI σ hσ.1 hc, ?_⟩
      rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hls,
          hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ |
        ⟨N, N', ha, hb, hN, hN'⟩
      · have hclC := liftA_instantiateLevelsA_closed
          (envNormClosedA_getD hEN hE hcm hk) lsC
        have hclC' := liftA_instantiateLevelsA_closed
          (envNormClosedA_getD hEN hE hcm hk) lsC'
        rw [hCp] at hT hT' hargs
        refine Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁.map (wkExprA σ), ps₂.map (wkExprA σ),
          fs.map (wkExprA σ), fs'.map (wkExprA σ), wkExprA σ T, wkExprA σ T',
          hcm, hk, hfam, ?_, hls, hkinds, ?_, ?_, ?_, by simp [hp₁], by simp [hp₂], ?_, ?_, ?_, ?_, ?_⟩
        · rw [carrierLevelsA_wk]; exact hlC
        · rw [carrierParamsA_wk, hCp, applyTelA_wk_closed σ ps hclC, hT]; rfl
        · rw [carrierParamsA_wk, hCp, applyTelA_wk_closed σ ps hclC', hT']; rfl
        · obtain ⟨lsA, lsR, lsR', xsA, isR, isR', TF, Rres, Rres', hspA, hTF, hta, hspR, hlsA, hw,
            hta', hspR', hlsA', hw'⟩ := hcoh
          have hpsC : xsA.take m.nparamsA = ps := by
            rw [← hCp]; simp only [carrierParamsA, hspA]
          have hlsAC : carrierLevelsA C = lsA := by simp only [carrierLevelsA, hspA]
          have hl₀A : eqNListB n ls₀ lsA := ⟨hlsAC ▸ hCl, hlsAC ▸ hlC.2⟩
          have hclF := liftA_instantiateLevelsA_closed (hE r m hm).1 lsA
          rw [hpsC] at hTF hspR hw hspR' hw'
          refine ⟨lsA, lsR, lsR', xsA.map (wkExprA σ), isR.map (wkExprA σ), isR'.map (wkExprA σ),
            wkExprA σ TF, wkExprA σ Rres, wkExprA σ Rres', ?_, ?_, ?_, ?_, hlsA, ?_, ?_, ?_, hlsA', ?_⟩
          · simp only [appsSpineA_wkExprA, hspA, wkExprA_const]
          · rw [← List.map_take, hpsC, applyTelA_wk_closed σ ps hclF, hTF]; rfl
          · rw [applyTelA_wk σ fs T, hta]; rfl
          · simp only [appsSpineA_wkExprA, hspR, wkExprA_const, List.map_append, ← List.map_take, hpsC]
          · rw [← List.map_take, hpsC, ← List.map_drop]
            have hw2 := argsRelPA_wk σ (hcompF lsA TF · · · · · · · · hl₀A hTF) hw (pre := []) (pre' := [])
              (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
            simpa using hw2
          · rw [applyTelA_wk σ fs' T', hta']; rfl
          · simp only [appsSpineA_wkExprA, hspR', wkExprA_const, List.map_append, ← List.map_take, hpsC]
          · rw [← List.map_take, hpsC, ← List.map_drop]
            have hw2 := argsRelPA_wk σ (hcompF lsA TF · · · · · · · · hl₀A hTF) hw' (pre := []) (pre' := [])
              (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
            simpa using hw2
        · have h' := tyHRedStarA_wk hE hI σ hσ.1 ha
          rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at h'
          exact h'
        · have h' := tyHRedStarA_wk hE hI σ hσ.1 hb
          rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at h'
          exact h'
        · have h' := hStepFnA_wk_none hE hI Γ σ hσ.1 hna
          rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at h'
          exact h'
        · have h' := hStepFnA_wk_none hE hI Γ σ hσ.1 hnb
          rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at h'
          exact h'
        · rw [carrierParamsA_wk, hCp, carrierLevelsA_wk]
          have hlsA₀ : eqNList ls₀ (carrierLevelsA C) := hCl
          have hargs' := argsRelA_wk σ kinds (fun D x y hd => (hX D x y hd).2)
            (fun i prev A' j f f' hF0 => ⟨fun ρ'' hρ'' ys ys' C' hys hlen hC' => by
              have hρc : WkOkA E I n (WkSpecA.comp σ ρ'') (wkCtxA [] Γ) := wkOkA_comp hσ hρ''
              simp only [innerRelsA] at hys
              rw [map_wkExprA_comp, ← wkExprA_comp] at hys
              rw [← wkExprA_comp] at hC'
              have h0 := hF0.1 (WkSpecA.comp σ ρ'') hρc ys ys' C' (by simpa only [innerRelsA] using hys) hlen hC'
              refine ⟨?_, h0.2.1, ?_⟩
              · rw [map_wkExprA_comp]; exact h0.1
              · rw [← wkExprA_comp, ← wkExprA_comp]; exact h0.2.2.1, declPairA_wk hE hI hσ hF0.2⟩)
            (fun ksPre ks pre pre' D uD C' vC f f' hk' hp hp' hT₀ hR =>
              hcomp c cm lsC (carrierLevelsA C) kinds ksPre ks T pre pre' D uD C' vC f f' hcm hk hfam
                hkinds hk' hlsA₀ hlC.1 hT
                (argsRelA_mono (fun D x y hd => (hX D x y hd).1)
                  (famFunRelA_mono (fun _ _ _ _ _ hd => ⟨hd.1, hd.2.1, hd.2.2.1⟩)) hp) hp' hT₀ hR)
            hargs.1 [] [] [] (by simp) (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
          have hP₁ := convArgsA_wk hE hI σ hσ.1 hargs.2.1
          have hP₂ := convArgsA_wk hE hI σ hσ.1 hargs.2.2
          rw [wkExprA_closed (liftA_instantiateLevelsA_closed (hE r m hm).1 lsC)] at hP₁
          rw [wkExprA_closed (liftA_instantiateLevelsA_closed (hE r m hm).1 lsC')] at hP₂
          exact ⟨by simpa using hargs', hP₁, hP₂⟩
      · exact Or.inr ⟨wkExprA σ N, wkExprA σ N', tyHRedStarA_wk hE hI σ hσ.1 ha,
          tyHRedStarA_wk hE hI σ hσ.1 hb, stuckTmA_wk hE hI σ hσ.1 hN, stuckTmA_wk hE hI σ hσ.1 hN'⟩)
  exact (hY.2 rfl hAp hAl)

/-- **the fixed point of a clause weakened to `σ` is the clause's own, read at the composed
    world**: the operator over worlds of the weakened clause (its data at `σ ∘ ρ`, its context
    `wkCtxA σ Γ`) is the original's at `σ ∘ ρ`, since `wkCtxA (σ ∘ ρ) Γ = wkCtxA ρ (wkCtxA σ Γ)`.
    (R-NoFunRec-1 step 1 (1a).) -/
theorem lfpWA_reindex {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA}
    (σ ρ : WkSpecA) :
    LfpWA (FamPhiWA E I n (wkCtxA σ Γ) r m (fun ρ => Rs (WkSpecA.comp σ ρ))
        (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ))) ρ =
      LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp σ ρ) := by
  funext A a b
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · exact h (fun ρ C a b => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp σ ρ) C a b)
      (fun ρ C a b hs => LfpWA.fold famPhiWA_mono (by
        have key : (fun c lsC => innerRelsA RsI (WkSpecA.comp σ ρ) c lsC) =
            (fun c lsC => innerRelsA (fun ρ => RsI (WkSpecA.comp σ ρ)) ρ c lsC) := by
          funext c lsC i prev ρ'
          simp only [innerRelsA, WkSpecA.comp_assoc]
        have key2 : (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp (WkSpecA.comp σ ρ) ρ')) =
            (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp σ (WkSpecA.comp ρ ρ'))) := by
          funext ρ'
          rw [WkSpecA.comp_assoc]
        show FamPhiA E I n (wkCtxA (WkSpecA.comp σ ρ) Γ) r m (Rs (WkSpecA.comp σ ρ))
          (RsF (WkSpecA.comp σ ρ)) (fun c lsC => innerRelsA RsI (WkSpecA.comp σ ρ) c lsC)
          (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp σ ρ))
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp (WkSpecA.comp σ ρ) ρ')) C a b
        rw [key, key2, wkCtxA_comp]; exact hs))
  · have hY := h (fun w C a b => ∀ ρ, w = WkSpecA.comp σ ρ →
        LfpWA (FamPhiWA E I n (wkCtxA σ Γ) r m (fun ρ => Rs (WkSpecA.comp σ ρ))
          (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ))) ρ C a b)
      (fun w C a b hs ρ hw => by
        subst hw
        refine LfpWA.fold famPhiWA_mono ?_
        have key : (fun c lsC => innerRelsA (fun ρ => RsI (WkSpecA.comp σ ρ)) ρ c lsC) =
            (fun c lsC => innerRelsA RsI (WkSpecA.comp σ ρ) c lsC) := by
          funext c lsC i prev ρ'
          simp only [innerRelsA, WkSpecA.comp_assoc]
        show FamPhiA E I n (wkCtxA ρ (wkCtxA σ Γ)) r m (Rs (WkSpecA.comp σ ρ)) (RsF (WkSpecA.comp σ ρ))
          (fun c lsC => innerRelsA (fun ρ => RsI (WkSpecA.comp σ ρ)) ρ c lsC)
          (LfpWA (FamPhiWA E I n (wkCtxA σ Γ) r m (fun ρ => Rs (WkSpecA.comp σ ρ))
            (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ))) ρ)
          (fun ρ' => LfpWA (FamPhiWA E I n (wkCtxA σ Γ) r m (fun ρ => Rs (WkSpecA.comp σ ρ))
            (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ))) (WkSpecA.comp ρ ρ')) C a b
        rw [key, ← wkCtxA_comp]
        exact famPhiA_mono (fun _ _ _ h => h ρ rfl)
          (fun ρ' _ _ _ _ h => h (WkSpecA.comp ρ ρ') (WkSpecA.comp_assoc σ ρ ρ')) hs)
    exact hY ρ rfl

end FamWk

#print axioms tyHRedStarA_wk
#print axioms stuckTmA_wk
#print axioms argsRelA_wk
#print axioms lfpWA_wk
#print axioms lfpWA_reindex

end Rcic.Declarative.Ann
