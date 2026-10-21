import rcic.RcicSynClauseAlg
import rcic.RcicSynInstEnd

/-!
# Syntactic sortRow, build step 3y — `.yes` erases to the clause

`research/rcic/semantic/S3_ES_ARMS.md` §24. `readRedex` on `.yes` pushes
`wk` / `esub` / `linst` into the extracted body and argument. §23 transports
a clause that is already the inner erasure. This module is the other half:
the pushed typing erases to that transported clause.

A pure `app` of a pure `lam` is the base. `wk` (skip, proof domain, relevant
domain) and `esub` under the redex (drop, and keep when the replacement is
not `★`) preserve the equation. `linst` recomputes `σ`.

Not this module: `esub` whose term is the variable. On the `drop` path that
derivation erases to `★` (`esub_bvar_drop_star`), and the reader returns the
replacement (`esub_bvar_drop_ne`). On the `keep` path the variable has to
erase to `bvar (countKeep (ρ.take j))` before `inst` hits, and that is not
a clause of `TyP.eps`. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

theorem eps_tyCastCtx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {e T : Expr Nat}
    (hΓ : Γ = Γ') (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    (tyCastCtx hΓ D).eps σ ρ = D.eps σ ρ := by
  cases hΓ
  rfl

theorem get?_not_keep_succ {d : Disp} {ρ : List Disp} {c : Nat}
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) :
    (d :: ρ)[c + 1]? = none ∨ (d :: ρ)[c + 1]? = some .drop ∨
      ∃ v, (d :: ρ)[c + 1]? = some (.inline v) := by
  simpa [List.get?_cons_succ] using hk

theorem eps_pushBody_drop {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (σ : Level → Level) (ρb : List Disp) (hu : levelIsZero (σ uE) = true) :
    (pushBodyEsub hbody hget hv hvT hAe hBe).eps σ ρb =
      hbody.eps σ (insertDisp .drop (j + 1) ρb) := by
  unfold pushBodyEsub
  rw [eps_tyCastCtx, eps_tyCast, eps_esub_drop (hu := hu)]

/-- A proof variable, substituted on the `drop` path, erases to `★`. -/
theorem esub_bvar_drop_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A t v : Expr Nat} {j : Nat} {u : Level}
    (hlook : lookupType Γ j = some A) (hA : TyP E n Γ A (.sort u))
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (σ : Level → Level) (ρ : List Disp) (hu : levelIsZero (σ u) = true) :
    (TyP.esub E n Γ (.bvar j) A t v j u
        (TyP.bvar E n Γ j A u hlook hA) hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_drop (hu := hu), eps_bvar_proof hu]

/-- The reader returns the replacement. The `drop` derivation does not. -/
theorem esub_bvar_drop_ne {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A t v : Expr Nat} {j : Nat} {u : Level}
    (hlook : lookupType Γ j = some A) (hA : TyP E n Γ A (.sort u))
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (σ : Level → Level) (ρ : List Disp) (hu : levelIsZero (σ u) = true)
    (hne : hv.eps σ ρ ≠ .star) :
    (TyP.esub E n Γ (.bvar j) A t v j u
        (TyP.bvar E n Γ j A u hlook hA) hget hv hvT).eps σ ρ ≠ hv.eps σ ρ := by
  rw [esub_bvar_drop_star hlook hA hget hv hvT σ ρ hu]
  exact Ne.symm hne

theorem linst_redex_yes {E : ResolvedEnv} {a n : Nat} {Γ₀ : LCtx} {e T₀ : Expr Nat}
    {ls : List Level} (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D : TyP E a Γ₀ e T₀)
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E a Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
    (ha : instantiateLevels ls a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hD : D.eps (fun l => σ (instLevel ls l)) ρ =
      redexClause (levelIsZero (σ (instLevel ls g.u)))
        (g.hbody.eps (fun l => σ (instLevel ls l))
          (binderDisp (levelIsZero (σ (instLevel ls g.u))) :: ρ))
        (g.harg.eps (fun l => σ (instLevel ls l)) ρ)) :
    (TyP.linst E a n Γ₀ e T₀ ls hls hlen D).eps σ ρ =
      redexClause (levelIsZero (σ (instLevel ls g.u)))
        ((tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
              (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
            (tyCast hb rfl
              (TyP.linst E a n (.assumption A₀ :: Γ₀) b₀ g.B ls hls hlen g.hbody))).eps
          σ (binderDisp (levelIsZero (σ (instLevel ls g.u))) :: ρ))
        ((tyCast ha rfl
            (TyP.linst E a n Γ₀ a₀ g.Aarg ls hls hlen g.harg)).eps σ ρ) := by
  rw [eps_linst, hD, eps_tyCastCtx, eps_tyCast, eps_linst, eps_tyCast, eps_linst]

theorem wk_redex_skip {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP E n Γ₀ e T)
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (hD : D.eps σ (removeAt ρ c) =
      redexClause (levelIsZero (σ g.u))
        (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: removeAt ρ c))
        (g.harg.eps σ (removeAt ρ c))) :
    (TyP.wk E n Γ₀ e T d c D).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ) := by
  have harg :
      (tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ =
        g.harg.eps σ (removeAt ρ c) := by
    rw [eps_tyCast, eps_wk_not_keep hk]
  have hbody :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hb rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
        σ (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: removeAt ρ c) := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_not_keep (get?_not_keep_succ hk)]
    rfl
  rw [eps_wk_not_keep hk, hD, hbody, harg]

theorem wk_redex_drop {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP E n Γ₀ e T)
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (removeAt ρ c) =
      redexClause (levelIsZero (σ g.u))
        (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: removeAt ρ c))
        (g.harg.eps σ (removeAt ρ c))) :
    (TyP.wk E n Γ₀ e T d c D).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ) := by
  simp only [hu, binderDisp] at *
  have hkB : (.drop :: ρ)[c + 1]? = some .keep := by
    simpa [List.get?_cons_succ] using hk
  have harg :
      (tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ =
        (g.harg.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
    rw [eps_tyCast, eps_wk_keep hk]
  have hbody :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hb rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
        σ (.drop :: ρ) =
        (g.hbody.eps σ (.drop :: removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, lift_redexClause_drop, hbody, harg]

theorem wk_redex_keep {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP E n Γ₀ e T)
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (removeAt ρ c) =
      redexClause (levelIsZero (σ g.u))
        (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: removeAt ρ c))
        (g.harg.eps σ (removeAt ρ c))) :
    (TyP.wk E n Γ₀ e T d c D).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ) := by
  simp only [hu, binderDisp] at *
  have hkB : (.keep :: ρ)[c + 1]? = some .keep := by
    simpa [List.get?_cons_succ] using hk
  have harg :
      (tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ =
        (g.harg.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
    rw [eps_tyCast, eps_wk_keep hk]
  have hbody :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hb rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
        σ (.keep :: ρ) =
        (g.hbody.eps σ (.keep :: removeAt ρ c)).lift (countKeep (ρ.take c) + 1) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, lift_redexClause_keep, hbody, harg]

theorem esub_redex_drop_yes {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP E n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    (hD : D.eps σ (insertDisp .drop j ρ) =
      redexClause (levelIsZero (σ g.u))
        (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: insertDisp .drop j ρ))
        (g.harg.eps σ (insertDisp .drop j ρ))) :
    (TyP.esub E n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget hv hvT hAe hBe).eps σ
          (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hv hvT)).eps σ ρ) := by
  have harg :
      (tyCast haEq rfl
          (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hv hvT)).eps σ ρ =
        g.harg.eps σ (insertDisp .drop j ρ) := by
    rw [eps_tyCast, eps_esub_drop (hu := hu)]
  have hbody :
      (pushBodyEsub g.hbody hget hv hvT hAe hBe).eps σ
          (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: insertDisp .drop j ρ) := by
    rw [eps_pushBody_drop _ _ _ _ _ _ _ (hu := hu)]
    rfl
  rw [eps_esub_drop (hu := hu), hD, hbody, harg]

/-- Proof binder: the pushed body instantiates at the same erased index as
    the argument, and the replacement is not lifted. -/
theorem eps_pushBody_keep_drop {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (σ : Level → Level) (ρ : List Disp) (hu : levelIsZero (σ uE) = false) :
    (pushBodyEsub hbody hget hv hvT hAe hBe).eps σ (.drop :: ρ) =
      ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
        (hbody.eps σ (.drop :: insertDisp .keep j ρ)) := by
  unfold pushBodyEsub
  rw [eps_tyCastCtx, eps_tyCast, eps_esub_keep (hu := hu)]
  have hidx : countKeep ((.drop :: ρ).take (j + 1)) = countKeep (ρ.take j) := by
    simp only [List.take_succ_cons, countKeep]
  have hrep :
      (tyCastCtx ((substRemove_cod_eq repl j A₀ A Γ₀ hAe).symm)
          (tyCast (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) repl)
            (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t)
            (TyP.wk E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              (.assumption A) 0 hv))).eps σ (.drop :: ρ) =
        hv.eps σ ρ := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_not_keep]
    · rfl
    · apply Or.inr
      apply Or.inl
      simp [List.get?_cons_zero]
  have hbodyρ :
      hbody.eps σ (insertDisp .keep (j + 1) (.drop :: ρ)) =
        hbody.eps σ (.drop :: insertDisp .keep j ρ) := rfl
  rw [hidx, hrep, hbodyρ]

/-- Relevant binder: the body is one erased slot deeper, and the replacement
    is lifted across that slot. -/
theorem eps_pushBody_keep_keep {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (σ : Level → Level) (ρ : List Disp) (hu : levelIsZero (σ uE) = false) :
    (pushBodyEsub hbody hget hv hvT hAe hBe).eps σ (.keep :: ρ) =
      ETm.inst (countKeep (ρ.take j) + 1) ((hv.eps σ ρ).lift 0 1)
        (hbody.eps σ (.keep :: insertDisp .keep j ρ)) := by
  unfold pushBodyEsub
  rw [eps_tyCastCtx, eps_tyCast, eps_esub_keep (hu := hu)]
  have hidx : countKeep ((.keep :: ρ).take (j + 1)) = countKeep (ρ.take j) + 1 := by
    simp only [List.take_succ_cons, countKeep]
  have hrep :
      (tyCastCtx ((substRemove_cod_eq repl j A₀ A Γ₀ hAe).symm)
          (tyCast (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) repl)
            (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t)
            (TyP.wk E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              (.assumption A) 0 hv))).eps σ (.keep :: ρ) =
        (hv.eps σ ρ).lift 0 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep]
    · simp only [List.take_zero, countKeep, removeAt]
    · simp [List.get?_cons_zero]
  have hbodyρ :
      hbody.eps σ (insertDisp .keep (j + 1) (.keep :: ρ)) =
        hbody.eps σ (.keep :: insertDisp .keep j ρ) := rfl
  rw [hidx, hrep, hbodyρ]

theorem esub_redex_keep_drop {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP E n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false) (hr : hv.eps σ ρ ≠ .star)
    (_hbit : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (insertDisp .keep j ρ) =
      redexClause true
        (g.hbody.eps σ (.drop :: insertDisp .keep j ρ))
        (g.harg.eps σ (insertDisp .keep j ρ))) :
    (TyP.esub E n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      redexClause true
        ((pushBodyEsub g.hbody hget hv hvT hAe hBe).eps σ (.drop :: ρ))
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hv hvT)).eps σ ρ) := by
  have harg :
      (tyCast haEq rfl
          (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hv hvT)).eps σ ρ =
        ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (g.harg.eps σ (insertDisp .keep j ρ)) := by
    rw [eps_tyCast, eps_esub_keep (hu := hu)]
  have hbody :
      (pushBodyEsub g.hbody hget hv hvT hAe hBe).eps σ (.drop :: ρ) =
        ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (g.hbody.eps σ (.drop :: insertDisp .keep j ρ)) :=
    eps_pushBody_keep_drop g.hbody hget hv hvT hAe hBe σ ρ hu
  rw [eps_esub_keep (hu := hu), hD, inst_redexClause_drop hr, hbody, harg]

theorem esub_redex_keep_keep {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP E n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false) (hr : hv.eps σ ρ ≠ .star)
    (_hbit : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (insertDisp .keep j ρ) =
      redexClause false
        (g.hbody.eps σ (.keep :: insertDisp .keep j ρ))
        (g.harg.eps σ (insertDisp .keep j ρ))) :
    (TyP.esub E n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      redexClause false
        ((pushBodyEsub g.hbody hget hv hvT hAe hBe).eps σ (.keep :: ρ))
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hv hvT)).eps σ ρ) := by
  have harg :
      (tyCast haEq rfl
          (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hv hvT)).eps σ ρ =
        ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (g.harg.eps σ (insertDisp .keep j ρ)) := by
    rw [eps_tyCast, eps_esub_keep (hu := hu)]
  have hbody :
      (pushBodyEsub g.hbody hget hv hvT hAe hBe).eps σ (.keep :: ρ) =
        ETm.inst (countKeep (ρ.take j) + 1) ((hv.eps σ ρ).lift 0 1)
          (g.hbody.eps σ (.keep :: insertDisp .keep j ρ)) :=
    eps_pushBody_keep_keep g.hbody hget hv hvT hAe hBe σ ρ hu
  rw [eps_esub_keep (hu := hu), hD, inst_redexClause_keep hr, hbody, harg]

theorem readRedex_app_clause (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    {arg : Expr Nat} {w : Level}
    (ha : TyP E n Γ arg A)
    (hT : TyP E n Γ (instantiate0 arg B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    match readRedex (envExt_refl E) Aw
        (TyP.app E n Γ (.lam A body) arg A B w
          (TyP.lam E n Γ A u body B v hA hbody hB) ha hT) rfl with
    | .yes g =>
        (TyP.app E n Γ (.lam A body) arg A B w
            (TyP.lam E n Γ A u body B v hA hbody hB) ha hT).eps σ ρ =
          redexClause (levelIsZero (σ g.u))
            (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
            (g.harg.eps σ ρ)
    | .no => False := by
  rw [eps_beta_node]
  rfl

end Rcic.Syn

#print axioms Rcic.Syn.eps_tyCastCtx
#print axioms Rcic.Syn.get?_not_keep_succ
#print axioms Rcic.Syn.eps_pushBody_drop
#print axioms Rcic.Syn.esub_bvar_drop_star
#print axioms Rcic.Syn.esub_bvar_drop_ne
#print axioms Rcic.Syn.linst_redex_yes
#print axioms Rcic.Syn.wk_redex_skip
#print axioms Rcic.Syn.wk_redex_drop
#print axioms Rcic.Syn.wk_redex_keep
#print axioms Rcic.Syn.esub_redex_drop_yes
#print axioms Rcic.Syn.eps_pushBody_keep_drop
#print axioms Rcic.Syn.eps_pushBody_keep_keep
#print axioms Rcic.Syn.esub_redex_keep_drop
#print axioms Rcic.Syn.esub_redex_keep_keep
#print axioms Rcic.Syn.readRedex_app_clause

