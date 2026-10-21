import rcic.RcicSynPiLamRight
import rcic.RcicSynPBitAll
import rcic.RcicSynAppWalk

/-!
# Syntactic sortRow, build step 3av — `PiVerdict` / `epsWalkPi`, plus same-constructor `CL` and `EUT` coherence across `TyP`

`research/rcic/semantic/S3_ES_ARMS.md` §48. This module completes the erasure
walk of `readPi` (`PiVerdict` / `epsWalkPi`, parallel to `LamVerdict` /
`epsWalkLam` in `RcicSynRead` and `AppVerdict` / `epsWalkApp` in `RcicSynAppWalk`),
and proves the same-constructor `CL` and `EUT` coherence lemmas across `TyP`:

1. **`PiVerdict` and clause transport for `PiGot` (`wk_pi_skip`, `wk_pi_keep`,
   `linst_pi_yes`, `esub_pi_drop`, `esub_pi_keep`)**:
   - `PiVerdict` records `.clause`, `.star`, `.raw`, and `.none` over `PiRead`.
   - `wk_pi_skip` and `wk_pi_keep` transport `piClauseOf` across `TyP.wk`.
   - `linst_pi_yes` transports `piClauseOf` across `TyP.linst`.
   - `esub_pi_drop` and `esub_pi_keep` transport `piClauseOf` across `TyP.esub`
     using `eps_pushBody_drop` and `eps_pushBody_keep_keep`.

2. **The `epsWalkPi` walk (`piVerdict_node`, `piVerdict_conv`, `piVerdict_ewk`,
   `piVerdict_wk`, `piVerdict_linst`, `piVerdict_esub_drop`,
   `piVerdict_esub_keep`, `piVerdict_bare`, `epsWalkPi`)**:
   - Total structural recursion over `D : TyP Ei n Γ e T` returning
     `PiVerdict D σ ρ (readPi hext Aw src D he hAt)`.

3. **Same-constructor `CL` and `EUT` coherence across `TyP` (`cl_sort_nodes`,
   `eut_sort_nodes`, `cl_bvar_nodes`, `cl_const_nodes`, `cl_pi_nodes`,
   `eut_pi_nodes`, `cl_lam_nodes_drop`, `cl_lam_nodes_keep`,
   `cl_lam_nodes_keep_star`, `eut_lam_nodes`, `cl_app_nodes_rel`,
   `cl_app_nodes_arg_star`, `cl_app_nodes_fun_star`, `cl_lit_nodes`,
   `cl_conv_left`, `cl_conv_right`)**:
   - Every non-transport `TyP` constructor pair on the same expression has its
     `CL` and `EUT` obligations discharged from subderivation `CL` / `BitCoh` /
     `SortCoh` / `PBit`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `PiVerdict` and clause transport for `PiGot` -/

/-- Erasure of `D` against the reading of a `Π`-type. `raw` is a `.yes`
    the walk does not identify. -/
inductive PiVerdict {Ei : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP Ei n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    {Aw : Nat → Nat} → {src : Nat} → {E : ResolvedEnv} → {A B : Expr Nat} →
    PiRead Aw src E n Γ A B → Type where
  | clause {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A B : Expr Nat}
      {g : PiGot Aw src E n Γ A B}
      (h : D.eps σ ρ = piClauseOf g σ ρ) : PiVerdict D σ ρ (.yes g)
  | star {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A B : Expr Nat}
      {g : PiGot Aw src E n Γ A B}
      (h : D.eps σ ρ = .star) : PiVerdict D σ ρ (.yes g)
  | raw {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A B : Expr Nat}
      {g : PiGot Aw src E n Γ A B} : PiVerdict D σ ρ (.yes g)
  | none {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A B : Expr Nat} :
      PiVerdict D σ ρ (PiRead.no : PiRead Aw src E n Γ A B)

/-- A `PiVerdict` moves onto another typing with the same erasure. -/
def PiVerdict.move {Ei Ei' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} {D : TyP Ei n Γ e T} {D' : TyP Ei' n Γ e' T'}
    {σ : Level → Level} {ρ : List Disp}
    {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A B : Expr Nat}
    {r : PiRead Aw src E n Γ A B}
    (heq : D'.eps σ ρ = D.eps σ ρ) : PiVerdict D σ ρ r → PiVerdict D' σ ρ r
  | .clause h => .clause (heq.trans h)
  | .star h => .star (heq.trans h)
  | .raw => .raw
  | .none => .none

theorem wk_pi_skip {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hA : lift c 1 A₀ = A) (hB : lift (c + 1) 1 B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (hD : D.eps σ (removeAt ρ c) = piClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      .pi ((tyCast hA rfl (TyP.wk E n Γ₀ A₀ (.sort g.u) d c g.hA)).eps σ ρ)
        (piSlot (levelIsZero (σ g.u))
          ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
              (tyCast hB rfl
                (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))).eps
            σ (binderDisp (levelIsZero (σ g.u)) :: ρ))) := by
  have hcod :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hB rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))).eps
        σ (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hB.eps σ (binderDisp (levelIsZero (σ g.u)) :: removeAt ρ c) := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_not_keep (get?_not_keep_succ hk)]
    rfl
  rw [eps_wk_not_keep hk, hD, eps_tyCast, eps_wk_not_keep hk, hcod]
  rfl

theorem wk_pi_keep {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hA : lift c 1 A₀ = A) (hB : lift (c + 1) 1 B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (removeAt ρ c) = piClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      .pi ((tyCast hA rfl (TyP.wk E n Γ₀ A₀ (.sort g.u) d c g.hA)).eps σ ρ)
        (piSlot (levelIsZero (σ g.u))
          ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
              (tyCast hB rfl
                (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))).eps
            σ (binderDisp (levelIsZero (σ g.u)) :: ρ))) := by
  simp only [hu, binderDisp, piSlot, piClauseOf] at hD ⊢
  have hkB : (.keep :: ρ)[c + 1]? = some .keep := by
    simpa [List.get?_cons_succ] using hk
  have hcod :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hB rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))).eps
        σ (.keep :: ρ) =
        (g.hB.eps σ (.keep :: removeAt ρ c)).lift
          (countKeep (ρ.take c) + 1) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, eps_tyCast, eps_wk_keep hk, hcod]
  rfl

/-- Proof-domain variant (S13_R2_SCOPE_AMENDMENT §6, S12 §6.1): with the
    Π-domain bit `true`, the binder display is `.drop` — it adds no erased
    slot, so the pushed codomain's `wk` lifts only across `ρ`'s own `keep`s;
    the outer `wk` lift then exchanges with the `piSlot` pad by `piSlot_lift`. -/
theorem wk_pi_keep_proof {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hA : lift c 1 A₀ = A) (hB : lift (c + 1) 1 B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (removeAt ρ c) = piClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      .pi ((tyCast hA rfl (TyP.wk E n Γ₀ A₀ (.sort g.u) d c g.hA)).eps σ ρ)
        (piSlot (levelIsZero (σ g.u))
          ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
              (tyCast hB rfl
                (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))).eps
            σ (binderDisp (levelIsZero (σ g.u)) :: ρ))) := by
  simp only [hu, binderDisp, piClauseOf] at hD ⊢
  have hkB : (.drop :: ρ)[c + 1]? = some .keep := by
    simpa [List.get?_cons_succ] using hk
  have hcod :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hB rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))).eps
        σ (.drop :: ρ) =
        (g.hB.eps σ (.drop :: removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, eps_tyCast, eps_wk_keep hk, hcod]
  simp only [ETm.lift]
  congr 1
  exact piSlot_lift true (countKeep (ρ.take c)) 1
    (g.hB.eps σ (.drop :: removeAt ρ c))

theorem linst_pi_yes {Em : ResolvedEnv} {a n : Nat} {Γ₀ : LCtx}
    {e T₀ : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D : TyP Em a Γ₀ e T₀)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E a Γ₀ A₀ B₀) {A B : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hB : instantiateLevels ls B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hD : D.eps (fun l => σ (instLevel ls l)) ρ =
      piClauseOf g (fun l => σ (instLevel ls l)) ρ) :
    (TyP.linst Em a n Γ₀ e T₀ ls hls hlen D).eps σ ρ =
      .pi
        ((tyCast hA rfl (TyP.linst E a n Γ₀ A₀ (.sort g.u) ls hls hlen g.hA)).eps σ ρ)
        (piSlot (levelIsZero (σ (instLevel ls g.u)))
          ((tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
                (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
              (tyCast hB rfl
                (TyP.linst E a n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) ls hls hlen g.hB))).eps
            σ (binderDisp (levelIsZero (σ (instLevel ls g.u))) :: ρ))) := by
  rw [eps_linst, hD, eps_tyCast, eps_tyCastCtx, eps_tyCast, eps_linst, eps_linst]
  rfl

theorem esub_pi_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    (hD : D.eps σ (insertDisp .drop j ρ) = piClauseOf g σ (insertDisp .drop j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      .pi
        ((tyCast hAe rfl
            (TyP.esub E n Γ₀ A₀ (.sort g.u) t repl j uE g.hA hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ)
        (piSlot (levelIsZero (σ g.u))
          ((pushBodyEsub g.hB hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT)
              hAe hBe).eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ))) := by
  have hcod :
      (pushBodyEsub g.hB hget
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
            hext hv)
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
            hext hvT)
          hAe hBe).eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hB.eps σ (binderDisp (levelIsZero (σ g.u)) :: insertDisp .drop j ρ) := by
    rw [eps_pushBody_drop _ _ _ _ _ _ _ (hu := hu)]
    rfl
  rw [eps_esub_drop (hu := hu), hD, eps_tyCast, eps_esub_drop (hu := hu), hcod]
  rfl

theorem esub_pi_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    (hbit : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (insertDisp .keep j ρ) = piClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      .pi
        ((tyCast hAe rfl
            (TyP.esub E n Γ₀ A₀ (.sort g.u) t repl j uE g.hA hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ)
        (piSlot (levelIsZero (σ g.u))
          ((pushBodyEsub g.hB hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT)
              hAe hBe).eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ))) := by
  simp only [hbit, binderDisp, piSlot, piClauseOf] at hD ⊢
  have hcod :=
    eps_pushBody_keep_keep g.hB hget
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
      hAe hBe σ ρ hu
  rw [eps_esub_keep (hu := hu), hD, eps_tyCast, eps_esub_keep (hu := hu), eps_ewk, hcod]
  rfl

/-- Proof-domain variant (S13 §6 amendment, S12 §6.1): the outer substitution
    still keeps (`levelIsZero (σ uE) = false`) but the Π's own domain bit is
    `true`, so the pushed body is transported under the `.drop` binder
    (`eps_pushBody_keep_drop` — no `+1`, no lifted replacement) and the keep
    splice exchanges with the `piSlot` pad by `piSlot_inst`. -/
theorem esub_pi_keep_proof {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ B₀ : Expr Nat}
    (g : PiGot Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    (hbit : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (insertDisp .keep j ρ) = piClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      .pi
        ((tyCast hAe rfl
            (TyP.esub E n Γ₀ A₀ (.sort g.u) t repl j uE g.hA hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ)
        (piSlot (levelIsZero (σ g.u))
          ((pushBodyEsub g.hB hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT)
              hAe hBe).eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ))) := by
  simp only [hbit, binderDisp, piClauseOf] at hD ⊢
  have hcod :=
    eps_pushBody_keep_drop g.hB hget
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
      hAe hBe σ ρ hu
  rw [eps_esub_keep (hu := hu), hD, eps_tyCast, eps_esub_keep (hu := hu), eps_ewk, hcod]
  simp only [ETm.inst]
  congr 1
  exact piSlot_inst true (countKeep (ρ.take j)) (hv.eps σ ρ)
    (g.hB.eps σ (.drop :: insertDisp .keep j ρ))

/-! ## §2 The `epsWalkPi` walk -/

def piVerdict_node {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    {u v : Level}
    (hA : TyP Ei n Γ A (.sort u)) (hB : TyP Ei n (.assumption A :: Γ) B (.sort v))
    (hAt : ∀ y ∈ (TyP.pi Ei n Γ A u B v hA hB).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp) :
    PiVerdict (TyP.pi Ei n Γ A u B v hA hB) σ ρ
      (readPi hext Aw src (TyP.pi Ei n Γ A u B v hA hB) rfl hAt) := by
  unfold readPi
  exact .clause (piOfNode_eps hext Aw src hA hB hAt σ ρ).symm

def piVerdict_conv {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx} {e X Y : Expr Nat} {u : Level}
    (inner : TyP Ei n Γ e X) (hc : CvP Ei n Γ X Y (.sort u))
    {A B : Expr Nat} (he : e = .pi A B)
    (hAt : ∀ y ∈ (TyP.conv Ei n Γ e X Y u inner hc).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    (ih : PiVerdict inner σ ρ
      (readPi hext Aw src inner he (conv_atom_src Aw inner hc hAt))) :
    PiVerdict (TyP.conv Ei n Γ e X Y u inner hc) σ ρ
      (readPi hext Aw src (TyP.conv Ei n Γ e X Y u inner hc) he hAt) := by
  unfold readPi
  exact ih.move (eps_conv σ ρ)

def piVerdict_ewk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {E₀ : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e X : Expr Nat} (hext' : EnvExt E₀ Ei) (inner : TyP E₀ n Γ e X)
    {A B : Expr Nat} (he : e = .pi A B)
    (hAt : ∀ y ∈ (TyP.ewk E₀ Ei n Γ e X hext' inner).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    (ih : PiVerdict inner σ ρ
      (readPi (envExt_trans hext' hext) Aw src inner he
        (ewk_atom_src Aw hext' inner hAt))) :
    PiVerdict (TyP.ewk E₀ Ei n Γ e X hext' inner) σ ρ
      (readPi hext Aw src (TyP.ewk E₀ Ei n Γ e X hext' inner) he hAt) := by
  unfold readPi
  exact ih.move (eps_ewk σ ρ)

def piVerdict_wk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d : LocalDecl} {c : Nat} (inner : TyP Ei n Γ₀ e₀ T₀)
    {A B : Expr Nat} (he : lift c 1 e₀ = .pi A B)
    (hAt : ∀ y ∈ (TyP.wk Ei n Γ₀ e₀ T₀ d c inner).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    {A₀ B₀ : Expr Nat} {he₀ : e₀ = .pi A₀ B₀}
    {hA₀ : lift c 1 A₀ = A} {hB₀ : lift (c + 1) 1 B₀ = B}
    (hF : lift_eq_pi he = .mk A₀ B₀ he₀ hA₀ hB₀)
    (ih : PiVerdict inner σ (removeAt ρ c)
      (readPi hext Aw src inner he₀ (wk_atom_src Aw inner hAt))) :
    PiVerdict (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) σ ρ
      (readPi hext Aw src (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) he hAt) := by
  unfold readPi
  rw [hF]
  dsimp
  cases hri : readPi hext Aw src inner he₀ (wk_atom_src Aw inner hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushPiWk]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushPiWk]
          exact .raw
      | star h =>
          simp only [pushPiWk]
          exact .star (eps_wk_star h)
      | clause h =>
          simp only [pushPiWk]
          cases hρ : ρ[c]? with
          | none =>
              refine .clause ?_
              simp only [piClauseOf]
              exact wk_pi_skip inner g hA₀ hB₀ σ ρ (Or.inl hρ) h
          | some disp =>
              cases disp with
              | drop =>
                  refine .clause ?_
                  simp only [piClauseOf]
                  exact wk_pi_skip inner g hA₀ hB₀ σ ρ (Or.inr (Or.inl hρ)) h
              | inline v =>
                  refine .clause ?_
                  simp only [piClauseOf]
                  exact wk_pi_skip inner g hA₀ hB₀ σ ρ (Or.inr (Or.inr ⟨v, hρ⟩)) h
              | keep =>
                  cases hgu : levelIsZero (σ g.u) with
                  | false =>
                      refine .clause ?_
                      simp only [piClauseOf]
                      exact wk_pi_keep inner g hA₀ hB₀ σ ρ hρ hgu h
                  | true =>
                      refine .clause ?_
                      simp only [piClauseOf]
                      exact wk_pi_keep_proof inner g hA₀ hB₀ σ ρ hρ hgu h

def piVerdict_linst {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {a n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {ls : List Level} (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (inner : TyP Ei a Γ₀ e₀ T₀)
    {A B : Expr Nat} (he : instantiateLevels ls e₀ = .pi A B)
    (hAt : ∀ y ∈ (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    {A₀ B₀ : Expr Nat} {he₀ : e₀ = .pi A₀ B₀}
    {hA₀ : instantiateLevels ls A₀ = A} {hB₀ : instantiateLevels ls B₀ = B}
    (hF : instantiateLevels_eq_pi he = .mk A₀ B₀ he₀ hA₀ hB₀)
    (ih : PiVerdict inner (fun l => σ (instLevel ls l)) ρ
      (readPi hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt))) :
    PiVerdict (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) σ ρ
      (readPi hext Aw src (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) he hAt) := by
  unfold readPi
  rw [hF]
  dsimp
  cases hri : readPi hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushPiLinst]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushPiLinst]
          exact .raw
      | star h =>
          simp only [pushPiLinst]
          exact .star (eps_linst_star h)
      | clause h =>
          simp only [pushPiLinst]
          refine .clause ?_
          simp only [piClauseOf]
          exact linst_pi_yes hls hlen inner g hA₀ hB₀ σ ρ h

def piVerdict_esub_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A B : Expr Nat} (he : instantiate j (lift 0 j repl) e = .pi A B)
    (hAt : ∀ y ∈ (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT).atoms Aw,
      y < src)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    {A₀ B₀ : Expr Nat} {he₀ : e = .pi A₀ B₀}
    {hA₀ : instantiate j (lift 0 j repl) A₀ = A}
    {hB₀ : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B}
    (hF : instantiate_eq_pi he = .under A₀ B₀ he₀ hA₀ hB₀)
    (ih : PiVerdict inner σ (insertDisp .drop j ρ)
      (readPi hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt))) :
    PiVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readPi hext Aw src
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he hAt) := by
  unfold readPi
  rw [hF]
  dsimp
  cases hri : readPi hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushPiEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushPiEsub]
          exact .raw
      | star h =>
          simp only [pushPiEsub]
          exact .star (eps_esub_drop_star hu h)
      | clause h =>
          simp only [pushPiEsub]
          refine .clause ?_
          simp only [piClauseOf]
          exact esub_pi_drop hext inner hget hv hvT g hA₀ hB₀ σ ρ hu h

def piVerdict_esub_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A B : Expr Nat} (he : instantiate j (lift 0 j repl) e = .pi A B)
    (hAt : ∀ y ∈ (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT).atoms Aw,
      y < src)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    {A₀ B₀ : Expr Nat} {he₀ : e = .pi A₀ B₀}
    {hA₀ : instantiate j (lift 0 j repl) A₀ = A}
    {hB₀ : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B}
    (hF : instantiate_eq_pi he = .under A₀ B₀ he₀ hA₀ hB₀)
    (ih : PiVerdict inner σ (insertDisp .keep j ρ)
      (readPi hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt))) :
    PiVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readPi hext Aw src
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he hAt) := by
  unfold readPi
  rw [hF]
  dsimp
  cases hri : readPi hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushPiEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushPiEsub]
          exact .raw
      | star h =>
          simp only [pushPiEsub]
          exact .star (eps_esub_keep_star hu h)
      | clause h =>
          cases hgu : levelIsZero (σ g.u) with
          | false =>
              simp only [pushPiEsub]
              refine .clause ?_
              simp only [piClauseOf]
              exact esub_pi_keep hext inner hget hv hvT g hA₀ hB₀ σ ρ hu hgu h
          | true =>
              simp only [pushPiEsub]
              refine .clause ?_
              simp only [piClauseOf]
              exact esub_pi_keep_proof hext inner hget hv hvT g hA₀ hB₀ σ ρ hu hgu h

/-- The substituted variable is the `Π`-type. -/
noncomputable def piVerdict_bare {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A B : Expr Nat} (he : instantiate j (lift 0 j repl) e = .pi A B)
    (hAt : ∀ y ∈ (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT).atoms Aw,
      y < src)
    (σ : Level → Level) (ρ : List Disp)
    (hs : e = .bvar j) (hr : lift 0 j repl = .pi A B)
    (hI : instantiate_eq_pi he = .here hs hr)
    (ihV : PiVerdict hv σ ρ
      (readPi hext Aw src hv hr (esub_val_src Aw inner hget hv hvT hAt))) :
    PiVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readPi hext Aw src
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he hAt) := by
  unfold readPi
  rw [hI]
  dsimp
  cases hri : readPi hext Aw src hv hr (esub_val_src Aw inner hget hv hvT hAt) with
  | no =>
    rw [hri] at ihV
    cases ihV
    exact .none
  | yes g =>
    rw [hri] at ihV
    cases bareHere (j := j) (uE := uE) inner hs σ ρ with
    | raw =>
      exact .raw
    | starDrop hu hInner =>
      refine .star ?_
      rw [eps_esub_drop (hu := hu), hInner]
    | starKeep hu hInner =>
      refine .star ?_
      rw [eps_esub_keep (hu := hu), hInner, inst_star]
    | hit hu hhit =>
      cases ihV with
      | raw =>
        exact .raw
      | star hV =>
        refine .star ?_
        rw [eps_esub_keep (hu := hu), hhit, inst_bvar_hit, hV]
      | clause hV =>
        refine .clause ?_
        rw [eps_esub_keep (hu := hu), hhit, inst_bvar_hit, hV]

set_option maxHeartbeats 800000 in
noncomputable def epsWalkPi {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    (src : Nat) (σ : Level → Level) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A B : Expr Nat} → (he : e = .pi A B) →
    (hAt : ∀ y ∈ D.atoms Aw, y < src) → (ρ : List Disp) →
    PiVerdict D σ ρ (readPi hext Aw src D he hAt)
  | _, _, _, _, .sort .., _, _, he, _, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _, _ => by cases he
  | _, _, _, _, .pi _ _ _ A u B v hA hB, _, _, he, hAt, ρ =>
      match A, B, he with
      | _, _, rfl => piVerdict_node hext Aw src hA hB hAt σ ρ
  | _, _, _, _, .lam .., _, _, he, _, _ => by cases he
  | _, _, _, _, .app .., _, _, he, _, _ => by cases he
  | _, _, _, _, .letE .., _, _, he, _, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, he, hAt, ρ =>
      piVerdict_conv hext Aw src inner hc he hAt σ ρ
        (epsWalkPi hext Aw src σ inner he (conv_atom_src Aw inner hc hAt) ρ)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, hAt, ρ =>
      match hF : lift_eq_pi he with
      | .mk A₀ B₀ he₀ hA₀ hB₀ =>
          piVerdict_wk hext Aw src inner he hAt σ ρ hF
            (epsWalkPi hext Aw src σ inner he₀ (wk_atom_src Aw inner hAt)
              (removeAt ρ c))
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, hAt, ρ =>
      match hF : instantiate_eq_pi he with
      | .under A₀ B₀ he₀ hA₀ hB₀ =>
          match hu : levelIsZero (σ uE) with
          | true =>
              piVerdict_esub_drop hext Aw src inner hget hv hvT he hAt σ ρ hu hF
                (epsWalkPi hext Aw src σ inner he₀
                  (esub_inner_src Aw inner hget hv hvT hAt) (insertDisp .drop j ρ))
          | false =>
              piVerdict_esub_keep hext Aw src inner hget hv hvT he hAt σ ρ hu hF
                (epsWalkPi hext Aw src σ inner he₀
                  (esub_inner_src Aw inner hget hv hvT hAt) (insertDisp .keep j ρ))
      | .here hs hr =>
          piVerdict_bare hext Aw src inner hget hv hvT he hAt σ ρ hs hr hF
            (epsWalkPi hext Aw src σ hv hr (esub_val_src Aw inner hget hv hvT hAt) ρ)
  | _, _, _, _, .lsub .., _, _, _, _, _ => by
      unfold readPi
      exact .none
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, hAt, ρ =>
      match hF : instantiateLevels_eq_pi he with
      | .mk A₀ B₀ he₀ hA₀ hB₀ =>
          piVerdict_linst hext Aw src hls hlen inner he hAt σ ρ hF
            (epsWalkPi hext Aw src (fun l => σ (instLevel ls l)) inner he₀
              (linst_atom_src Aw hls hlen inner hAt) ρ)
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he, hAt, ρ =>
      piVerdict_ewk hext Aw src hext' inner he hAt σ ρ
        (epsWalkPi (envExt_trans hext' hext) Aw src σ inner he
          (ewk_atom_src Aw hext' inner hAt) ρ)
  | _, _, _, _, .cctx .., _, _, _, _, _ => by
      unfold readPi
      exact .none

/-! ## §3 Same-constructor `CL` and `EUT` coherence across `TyP` -/

/-- `CL` on two `TyP.sort` nodes at the same `l` holds by reflexivity (zero recursive calls). -/
theorem cl_sort_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l)) :
    CL tbl σ ρ (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) := by
  unfold CL
  rw [eps_sort, eps_sort]
  exact .refl _

/-- `EUT` on two `TyP.sort` nodes at the same `l` holds from `LevelSub σ` (zero recursive calls). -/
theorem eut_sort_nodes (tbl : List CRule) {σ : Level → Level} (hσ : LevelSub σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l)) :
    EUT tbl σ ρ (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) := by
  unfold EUT
  simp only [TyP.reg, eps_sort]
  exact .eqv (.sort (hσ.eqN_map (eqN_trans h₁ (eqN_symm h₂))))

/-- `CL` on two `TyP.bvar` nodes at the same index `i` follows from `BitCoh σ hA₁ hA₂`
    (zero recursive calls beyond `BitCoh`). -/
theorem cl_bvar_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂)) :
    CL tbl σ ρ (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) := by
  unfold CL
  cases hzu : levelIsZero (σ u₁)
  · have hzu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hzu
    rw [eps_bvar_rel hzu, eps_bvar_rel hzu₂]
    exact .refl _
  · have hzu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hzu
    rw [eps_bvar_proof hzu, eps_bvar_proof hzu₂]
    exact .refl _

/-- `CL` on two `TyP.const` nodes at the same `(r, ls)` follows from `levelIsZero (σ u₁) = levelIsZero (σ u₂)`
    (zero recursive calls beyond `BitCoh`). -/
theorem cl_const_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level}
    {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
    (hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂)) :
    CL tbl σ ρ
      (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) := by
  unfold CL
  cases hzu : levelIsZero (σ u₁)
  · have hzu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hzu
    rw [eps_const_rel hzu, eps_const_rel hzu₂]
    exact .refl _
  · have hzu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hzu
    rw [eps_const_proof hzu, eps_const_proof hzu₂]
    exact .refl _

/-- `CL` on two `TyP.pi` nodes on `(A, B)` follows from `BitCoh σ hA₁ hA₂`,
    `CL tbl σ ρ hA₁ hA₂`, and `CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB₁ hB₂`. -/
theorem cl_pi_nodes (tbl : List CRule) (hTC : TableClosed tbl)
    (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (hbit : BitCoh σ hA₁ hA₂)
    (hclA : CL tbl σ ρ hA₁ hA₂)
    (hclB : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB₁ hB₂) :
    CL tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  unfold CL at hclA hclB ⊢
  unfold BitCoh at hbit
  rw [eps_pi_clause, eps_pi_clause, ← hbit]
  exact convMod_pi hclA (convMod_piSlot hTC _ hclB)

/-- `EUT` on two `TyP.pi` nodes on `(A, B)` follows from `eqN (σ (.imax u₁ v₁)) (σ (.imax u₂ v₂))`. -/
theorem eut_pi_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (hcoh : eqN (σ (.imax u₁ v₁)) (σ (.imax u₂ v₂))) :
    EUT tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  unfold EUT
  simp only [TyP.reg, eps_sort]
  exact .eqv (.sort hcoh)

/-- `CL` on two `TyP.lam` nodes on a proof domain (`levelIsZero (σ u₁) = true`). -/
theorem cl_lam_nodes_drop (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = true) (hbit : BitCoh σ hA₁ hA₂)
    (hclb : CL tbl σ (.drop :: ρ) hb₁ hb₂) :
    CL tbl σ ρ
      (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  have hu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hu₁
  unfold CL at hclb ⊢
  rw [eps_lam_drop hu₁, eps_lam_drop hu₂]
  exact hclb

/-- `CL` on two `TyP.lam` nodes on a relevant domain when neither body erases to `★`. -/
theorem cl_lam_nodes_keep (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hbit : BitCoh σ hA₁ hA₂)
    (hne₁ : hb₁.eps σ (.keep :: ρ) ≠ .star)
    (hne₂ : hb₂.eps σ (.keep :: ρ) ≠ .star)
    (hclb : CL tbl σ (.keep :: ρ) hb₁ hb₂) :
    CL tbl σ ρ
      (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  have hu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hu₁
  unfold CL at hclb ⊢
  rw [eps_lam_clause, eps_lam_clause, hu₁, hu₂, binderDisp_keep]
  unfold lamErasure
  rw [lamClause_of_ne hne₁, lamClause_of_ne hne₂]
  exact convMod_lam hclb

/-- `CL` on two `TyP.lam` nodes on a relevant domain when both bodies erase to `★`. -/
theorem cl_lam_nodes_keep_star (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hbit : BitCoh σ hA₁ hA₂)
    (hs₁ : hb₁.eps σ (.keep :: ρ) = .star)
    (hs₂ : hb₂.eps σ (.keep :: ρ) = .star) :
    CL tbl σ ρ
      (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  have hu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hu₁
  unfold CL
  rw [eps_lam_clause, eps_lam_clause, hu₁, hu₂, binderDisp_keep, hs₁, hs₂]
  exact .refl _

/-- `EUT` on two `TyP.lam` nodes on `(A, body)` follows from `BitCoh σ hA₁ hA₂`,
    `CL tbl σ ρ hA₁ hA₂`, and `ConvMod (EStep tbl) LvlEq` between the erased codomain
    typings `hB₁.eps` and `hB₂.eps` at `binderDisp (levelIsZero (σ u₁)) :: ρ`. -/
theorem eut_lam_nodes (tbl : List CRule) (hTC : TableClosed tbl)
    (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (hbit : BitCoh σ hA₁ hA₂)
    (hclA : CL tbl σ ρ hA₁ hA₂)
    (hconvB : ConvMod (EStep tbl) LvlEq
      (hB₁.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
      (hB₂.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))) :
    EUT tbl σ ρ
      (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  unfold EUT
  simp only [TyP.reg]
  unfold CL at hclA
  unfold BitCoh at hbit
  rw [eps_pi_clause, eps_pi_clause, ← hbit]
  exact convMod_pi hclA (convMod_piSlot hTC _ hconvB)

/-- `CL` on two `TyP.app` nodes on `(f, a)` when neither function nor argument erases to `★`. -/
theorem cl_app_nodes_rel (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hf_ne₁ : hf₁.eps σ ρ ≠ .star) (ha_ne₁ : ha₁.eps σ ρ ≠ .star)
    (hf_ne₂ : hf₂.eps σ ρ ≠ .star) (ha_ne₂ : ha₂.eps σ ρ ≠ .star)
    (hclf : CL tbl σ ρ hf₁ hf₂) (hcla : CL tbl σ ρ ha₁ ha₂) :
    CL tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  unfold CL at hclf hcla ⊢
  rw [eps_app_appClause, eps_app_appClause, appClause_app hf_ne₁ ha_ne₁, appClause_app hf_ne₂ ha_ne₂]
  exact convMod_app hclf hcla

/-- `CL` on two `TyP.app` nodes on `(f, a)` when both arguments erase to `★`. -/
theorem cl_app_nodes_arg_star (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (ha_s₁ : ha₁.eps σ ρ = .star) (ha_s₂ : ha₂.eps σ ρ = .star)
    (hclf : CL tbl σ ρ hf₁ hf₂) :
    CL tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  unfold CL at hclf ⊢
  rw [eps_app_appClause, eps_app_appClause, ha_s₁, ha_s₂, appClause_right_star, appClause_right_star]
  exact hclf

/-- `CL` on two `TyP.app` nodes on `(f, a)` when both functions erase to `★`. -/
theorem cl_app_nodes_fun_star (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hf_s₁ : hf₁.eps σ ρ = .star) (hf_s₂ : hf₂.eps σ ρ = .star) :
    CL tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  unfold CL
  rw [eps_app_appClause, eps_app_appClause, hf_s₁, hf_s₂]
  exact .refl _

/-- `CL` on two `TyP.lit` nodes is identical to `CL` on their expansions. -/
theorem cl_lit_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂) :
    CL tbl σ ρ (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) ↔
      CL tbl σ ρ hexp₁ hexp₂ :=
  Iff.rfl

/-- `CL` on `TyP.conv` on the left is identical to `CL` on the inner typing. -/
theorem cl_conv_left (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B T₂ : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (D₂ : TyP E n Γ e T₂) :
    CL tbl σ ρ (TyP.conv E n Γ e A B u h hc) D₂ ↔ CL tbl σ ρ h D₂ :=
  Iff.rfl

/-- `CL` on `TyP.conv` on the right is identical to `CL` on the inner typing. -/
theorem cl_conv_right (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ A B : Expr Nat} {u : Level}
    (D₁ : TyP E n Γ e T₁)
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) :
    CL tbl σ ρ D₁ (TyP.conv E n Γ e A B u h hc) ↔ CL tbl σ ρ D₁ h :=
  Iff.rfl

end Rcic.Syn

#print axioms Rcic.Syn.wk_pi_keep_proof
#print axioms Rcic.Syn.esub_pi_keep_proof
