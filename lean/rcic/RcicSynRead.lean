import rcic.RcicSynYes

/-!
# Syntactic sortRow, build step 3z — the erasure walk of a reading

`research/rcic/semantic/S3_ES_ARMS.md` §25. `readLam` / `readRedex` push
`conv`, `ewk`, `linst`, `wk` and `esub`-under into the extracted body
(and the argument). §24 transports a clause that is already the inner
erasure. This module feeds those lemmas back along the reader.

The result is not one equation. An `esub` whose term is the variable, on
the `drop` path, erases to `★` while the reader returns the replacement
(`esub_bvar_drop_ne`). `LamVerdict` / `RedexVerdict` record which claim
holds:

- `clause`: the derivation erases to `lamClauseOf` / `redexClauseOf` of
  the got the reader returned;
- `star`: it erases to `★`, and that is not the got's clause;
- `raw`: the reader returned `.yes` and this walk does not claim the
  erasure;
- `none`: the reader returned `.no`.

`esub`-here on `keep` is `eps_here_keep_hit` / `eps_here_keep_hit_redex`:
the variable has to erase to `bvar (countKeep (ρ.take j))` before `inst`
hits. The walk does not prove that of an arbitrary typing, so that spine
is `raw`. A bare proof `bvar` on `drop` is `eps_here_drop_bvar`. A
`cctx`, and an application born around a substituted λ, stay `.no`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 what a got erases to -/

def lamClauseOf {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body : Expr Nat} (g : LamGot Aw src E n Γ A body)
    (σ : Level → Level) (ρ : List Disp) : ETm :=
  lamErasure (levelIsZero (σ g.u))
    (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ))

def redexClauseOf {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg : Expr Nat} (g : RedexGot Aw src E n Γ A body arg)
    (σ : Level → Level) (ρ : List Disp) : ETm :=
  redexClause (levelIsZero (σ g.u))
    (g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
    (g.harg.eps σ ρ)

/-- Erasure of `D` against the reading of a λ. `raw` is a `.yes` the walk
    does not identify. -/
inductive LamVerdict {Ei : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP Ei n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    {Aw : Nat → Nat} → {src : Nat} → {E : ResolvedEnv} → {A body : Expr Nat} →
    LamRead Aw src E n Γ A body → Type where
  | clause {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body : Expr Nat}
      {g : LamGot Aw src E n Γ A body}
      (h : D.eps σ ρ = lamClauseOf g σ ρ) : LamVerdict D σ ρ (.yes g)
  | star {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body : Expr Nat}
      {g : LamGot Aw src E n Γ A body}
      (h : D.eps σ ρ = .star) : LamVerdict D σ ρ (.yes g)
  | raw {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body : Expr Nat}
      {g : LamGot Aw src E n Γ A body} : LamVerdict D σ ρ (.yes g)
  | none {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body : Expr Nat} :
      LamVerdict D σ ρ (LamRead.no : LamRead Aw src E n Γ A body)

/-- Erasure of `D` against the reading of an `app` of a `lam`. -/
inductive RedexVerdict {Ei : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP Ei n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    {Aw : Nat → Nat} → {src : Nat} → {E : ResolvedEnv} →
    {A body arg : Expr Nat} →
    RedexRead Aw src E n Γ A body arg → Type where
  | clause {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body arg : Expr Nat}
      {g : RedexGot Aw src E n Γ A body arg}
      (h : D.eps σ ρ = redexClauseOf g σ ρ) : RedexVerdict D σ ρ (.yes g)
  | star {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body arg : Expr Nat}
      {g : RedexGot Aw src E n Γ A body arg}
      (h : D.eps σ ρ = .star) : RedexVerdict D σ ρ (.yes g)
  | raw {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body arg : Expr Nat}
      {g : RedexGot Aw src E n Γ A body arg} : RedexVerdict D σ ρ (.yes g)
  | none {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A body arg : Expr Nat} :
      RedexVerdict D σ ρ (RedexRead.no : RedexRead Aw src E n Γ A body arg)

/-! ## §2 `★` is fixed by the transports -/

theorem eps_wk_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp}
    (h : D.eps σ (removeAt ρ c) = .star) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = .star := by
  cases hρ : ρ[c]? with
  | none =>
      rw [eps_wk_not_keep (Or.inl hρ), h]
  | some disp =>
      cases disp with
      | keep =>
          rw [eps_wk_keep hρ, h]
          rfl
      | drop =>
          rw [eps_wk_not_keep (Or.inr (Or.inl hρ)), h]
      | inline v =>
          rw [eps_wk_not_keep (Or.inr (Or.inr ⟨v, hρ⟩)), h]

theorem eps_linst_star {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {ls : List Level} {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    {D : TyP E a Γ e A} {σ : Level → Level} {ρ : List Disp}
    (h : D.eps (fun l => σ (instLevel ls l)) ρ = .star) :
    (TyP.linst E a n Γ e A ls hls hlen D).eps σ ρ = .star := by
  rw [eps_linst, h]

theorem eps_esub_drop_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true)
    (h : D.eps σ (insertDisp .drop j ρ) = .star) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_drop (hu := hu), h]

theorem eps_esub_keep_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false)
    (h : D.eps σ (insertDisp .keep j ρ) = .star) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_keep (hu := hu), h]
  rfl

/-! ## §3 a λ clause, transported

The outer derivation and the got need not share an environment: the reader
returns a got at the extended `E`, and `ewk` does not change `eps`. -/

theorem wk_lam_skip {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E n Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (hD : D.eps σ (removeAt ρ c) = lamClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      lamErasure (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ)) := by
  have hbody :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hb rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
        σ (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: removeAt ρ c) := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_not_keep (get?_not_keep_succ hk)]
    rfl
  rw [eps_wk_not_keep hk, hD]
  simp only [lamClauseOf]
  rw [hbody]

theorem wk_lam_drop {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E n Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (removeAt ρ c) = lamClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      lamErasure (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ)) := by
  simp only [hu, binderDisp, lamErasure, lamClauseOf] at hD ⊢
  have hkB : (.drop :: ρ)[c + 1]? = some .keep := by
    simpa [List.get?_cons_succ] using hk
  have hbody :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hb rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
        σ (.drop :: ρ) =
        (g.hbody.eps σ (.drop :: removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, ← hbody]

theorem wk_lam_keep {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E n Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (removeAt ρ c) = lamClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      lamErasure (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ)) := by
  simp only [hu, binderDisp, lamErasure, lamClauseOf] at hD ⊢
  have hkB : (.keep :: ρ)[c + 1]? = some .keep := by
    simpa [List.get?_cons_succ] using hk
  have hbody :
      (tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
          (tyCast hb rfl
            (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
        σ (.keep :: ρ) =
        (g.hbody.eps σ (.keep :: removeAt ρ c)).lift
          (countKeep (ρ.take c) + 1) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, lift_lamClause, ← hbody]

theorem linst_lam_yes {Em : ResolvedEnv} {a n : Nat} {Γ₀ : LCtx} {e T₀ : Expr Nat}
    {ls : List Level} (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D : TyP Em a Γ₀ e T₀)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E a Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hD : D.eps (fun l => σ (instLevel ls l)) ρ =
      lamClauseOf g (fun l => σ (instLevel ls l)) ρ) :
    (TyP.linst Em a n Γ₀ e T₀ ls hls hlen D).eps σ ρ =
      lamErasure (levelIsZero (σ (instLevel ls g.u)))
        ((tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
              (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
            (tyCast hb rfl
              (TyP.linst E a n (.assumption A₀ :: Γ₀) b₀ g.B ls hls hlen
                g.hbody))).eps
          σ (binderDisp (levelIsZero (σ (instLevel ls g.u))) :: ρ)) := by
  rw [eps_linst]
  simp only [lamClauseOf] at hD ⊢
  rw [hD, eps_tyCastCtx, eps_tyCast, eps_linst]

theorem esub_lam_drop_yes {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E n Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    (hD : D.eps σ (insertDisp .drop j ρ) = lamClauseOf g σ (insertDisp .drop j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      lamErasure (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT)
            hAe hBe).eps σ
          (binderDisp (levelIsZero (σ g.u)) :: ρ)) := by
  have hbody :
      (pushBodyEsub g.hbody hget
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
            hext hv)
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
            hext hvT)
          hAe hBe).eps σ
        (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hbody.eps σ
          (binderDisp (levelIsZero (σ g.u)) :: insertDisp .drop j ρ) := by
    rw [eps_pushBody_drop _ _ _ _ _ _ _ (hu := hu)]
    rfl
  rw [eps_esub_drop (hu := hu), hD]
  simp only [lamClauseOf]
  rw [hbody]

/-- Proof binder: `inst` of the bare body. A `★` replacement still commutes. -/
theorem esub_lam_keep_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E n Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    (hbit : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (insertDisp .keep j ρ) = lamClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      lamErasure (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT)
            hAe hBe).eps σ
          (binderDisp (levelIsZero (σ g.u)) :: ρ)) := by
  simp only [hbit, binderDisp, lamErasure, lamClauseOf] at hD ⊢
  have hbody :=
    eps_pushBody_keep_drop g.hbody hget
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
      hAe hBe σ ρ hu
  rw [eps_esub_keep (hu := hu), hD, hbody]
  rfl

/-- Relevant binder: `inst_lamClause`. The replacement must not be `★`. -/
theorem esub_lam_keep_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ : Expr Nat}
    (g : LamGot Aw src E n Γ₀ A₀ b₀)
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    (hr : hv.eps σ ρ ≠ .star)
    (hbit : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (insertDisp .keep j ρ) = lamClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      lamErasure (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT)
            hAe hBe).eps σ
          (binderDisp (levelIsZero (σ g.u)) :: ρ)) := by
  simp only [hbit, binderDisp, lamErasure, lamClauseOf] at hD ⊢
  have hbody :=
    eps_pushBody_keep_keep g.hbody hget
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
      (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
      hAe hBe σ ρ hu
  rw [eps_esub_keep (hu := hu), hD, inst_lamClause _ hr, hbody]
  rfl

/-! ## §4 the variable spine -/

/-- A proof variable on the `drop` path erases to `★`. The variable's sort
    and the substitution's sort need not be the same level. -/
theorem eps_here_drop_bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A t repl : Expr Nat} {j : Nat} {uE uB : Level}
    (hlook : lookupType Γ j = some A) (hA : TyP E n Γ A (.sort uB))
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ) (lift 0 j t) (.sort uE))
    (σ : Level → Level) (ρ : List Disp)
    (huE : levelIsZero (σ uE) = true) (huB : levelIsZero (σ uB) = true) :
    (TyP.esub E n Γ (.bvar j) A t repl j uE
        (TyP.bvar E n Γ j A uB hlook hA) hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_drop (hu := huE), eps_bvar_proof huB]

/-- `keep`-here is the clause of the replacement once the variable erases
    to the index `inst` hits. -/
theorem eps_here_keep_hit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t repl : Expr Nat} {j : Nat} {uE : Level}
    (inner : TyP E n Γ e A)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {Al body : Expr Nat}
    (g : LamGot Aw src E n (substRemove repl j Γ) Al body)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    (hhit : inner.eps σ (insertDisp .keep j ρ) = .bvar (countKeep (ρ.take j)))
    (hV : hv.eps σ ρ = lamClauseOf g σ ρ) :
    (TyP.esub E n Γ e A t repl j uE inner hget hv hvT).eps σ ρ =
      lamClauseOf g σ ρ := by
  rw [eps_esub_keep (hu := hu), hhit, inst_bvar_hit, hV]

theorem eps_here_keep_hit_redex {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t repl : Expr Nat} {j : Nat} {uE : Level}
    (inner : TyP E n Γ e A)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {Al body arg : Expr Nat}
    (g : RedexGot Aw src E n (substRemove repl j Γ) Al body arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    (hhit : inner.eps σ (insertDisp .keep j ρ) = .bvar (countKeep (ρ.take j)))
    (hV : hv.eps σ ρ = redexClauseOf g σ ρ) :
    (TyP.esub E n Γ e A t repl j uE inner hget hv hvT).eps σ ρ =
      redexClauseOf g σ ρ := by
  rw [eps_esub_keep (hu := hu), hhit, inst_bvar_hit, hV]

/-! ## §5 the λ walk -/

def lamVerdict_node {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {body B : Expr Nat} {v : Level}
    (hA : TyP Ei n Γ A (.sort u))
    (hbody : TyP Ei n (.assumption A :: Γ) body B)
    (hB : TyP Ei n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    LamVerdict (TyP.lam Ei n Γ A u body B v hA hbody hB) σ ρ
      (readLam hext Aw (TyP.lam Ei n Γ A u body B v hA hbody hB) rfl) := by
  unfold readLam
  refine .clause ?_
  rw [eps_lam_clause]
  rfl

def lamVerdict_conv {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (inner : TyP Ei n Γ e A) (hc : CvP Ei n Γ A B (.sort u))
    {Al body : Expr Nat} (he : e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    (ih : LamVerdict inner σ ρ (readLam hext Aw inner he)) :
    LamVerdict (TyP.conv Ei n Γ e A B u inner hc) σ ρ
      (readLam hext Aw (TyP.conv Ei n Γ e A B u inner hc) he) := by
  unfold readLam
  cases hri : readLam hext Aw inner he with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [LamRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [LamRead.raise]
          exact .raw
      | star h =>
          simp only [LamRead.raise]
          refine .star ?_
          rw [eps_conv, h]
      | clause h =>
          simp only [LamRead.raise]
          refine .clause ?_
          rw [eps_conv, h]
          rfl

def lamVerdict_ewk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (hext' : EnvExt E₀ Ei) (inner : TyP E₀ n Γ e A)
    {Al body : Expr Nat} (he : e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    (ih : LamVerdict inner σ ρ (readLam (envExt_trans hext' hext) Aw inner he)) :
    LamVerdict (TyP.ewk E₀ Ei n Γ e A hext' inner) σ ρ
      (readLam hext Aw (TyP.ewk E₀ Ei n Γ e A hext' inner) he) := by
  unfold readLam
  cases hri : readLam (envExt_trans hext' hext) Aw inner he with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [LamRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [LamRead.raise]
          exact .raw
      | star h =>
          simp only [LamRead.raise]
          refine .star ?_
          rw [eps_ewk, h]
      | clause h =>
          simp only [LamRead.raise]
          refine .clause ?_
          rw [eps_ewk, h]
          rfl

def lamVerdict_cctx {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u : Level}
    (D : TyP Ei n (.assumption A :: Γ) e T) (hA : CvP Ei n Γ A A' (.sort u))
    {Al body : Expr Nat} (he : e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp) :
    LamVerdict (TyP.cctx Ei n Γ e T A A' u D hA) σ ρ
      (readLam hext Aw (TyP.cctx Ei n Γ e T A A' u D hA) he) := by
  unfold readLam
  exact .none

def lamVerdict_wk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d : LocalDecl} {c : Nat} (inner : TyP Ei n Γ₀ e₀ T₀)
    {Al body : Expr Nat} (he : lift c 1 e₀ = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    {A₀ b₀ : Expr Nat} {he₀ : e₀ = .lam A₀ b₀}
    {hAe : lift c 1 A₀ = Al} {hb₀ : lift (c + 1) 1 b₀ = body}
    (hL : lift_eq_lam he = .mk A₀ b₀ he₀ hAe hb₀)
    (ih : LamVerdict inner σ (removeAt ρ c) (readLam hext Aw inner he₀)) :
    LamVerdict (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) σ ρ
      (readLam hext Aw (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) he) := by
  unfold readLam
  rw [hL]
  dsimp
  cases hri : readLam hext Aw inner he₀ with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushLamWk, LamRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushLamWk, LamRead.raise]
          exact .raw
      | star h =>
          simp only [pushLamWk, LamRead.raise]
          refine .star ?_
          exact eps_wk_star h
      | clause h =>
          simp only [pushLamWk, LamRead.raise]
          refine .clause ?_
          simp only [lamClauseOf]
          cases hρ : ρ[c]? with
          | none =>
              exact wk_lam_skip inner g hAe hb₀ σ ρ (Or.inl hρ) h
          | some disp =>
              cases disp with
              | drop =>
                  exact wk_lam_skip inner g hAe hb₀ σ ρ (Or.inr (Or.inl hρ)) h
              | inline v =>
                  exact wk_lam_skip inner g hAe hb₀ σ ρ
                    (Or.inr (Or.inr ⟨v, hρ⟩)) h
              | keep =>
                  cases hu : levelIsZero (σ g.u) with
                  | true =>
                      simpa [hu, binderDisp] using
                        wk_lam_drop inner g hAe hb₀ σ ρ hρ hu h
                  | false =>
                      simpa [hu, binderDisp] using
                        wk_lam_keep inner g hAe hb₀ σ ρ hρ hu h

def lamVerdict_linst {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {a n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {ls : List Level} (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (inner : TyP Ei a Γ₀ e₀ T₀)
    {Al body : Expr Nat} (he : instantiateLevels ls e₀ = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    {A₀ b₀ : Expr Nat} {he₀ : e₀ = .lam A₀ b₀}
    {hAe : instantiateLevels ls A₀ = Al} {hb₀ : instantiateLevels ls b₀ = body}
    (hL : instantiateLevels_eq_lam he = .mk A₀ b₀ he₀ hAe hb₀)
    (ih : LamVerdict inner (fun l => σ (instLevel ls l)) ρ
      (readLam hext Aw inner he₀)) :
    LamVerdict (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) σ ρ
      (readLam hext Aw (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) he) := by
  unfold readLam
  rw [hL]
  dsimp
  cases hri : readLam hext Aw inner he₀ with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushLamLinst, LamRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushLamLinst, LamRead.raise]
          exact .raw
      | star h =>
          simp only [pushLamLinst, LamRead.raise]
          refine .star ?_
          exact eps_linst_star h
      | clause h =>
          simp only [pushLamLinst, LamRead.raise]
          refine .clause ?_
          simp only [lamClauseOf]
          exact linst_lam_yes hls hlen inner g hAe hb₀ σ ρ h

def lamVerdict_esub_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body : Expr Nat} (he : instantiate j (lift 0 j repl) e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    {A₀ b₀ : Expr Nat} {he₀ : e = .lam A₀ b₀}
    {hAe : instantiate j (lift 0 j repl) A₀ = Al}
    {hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body}
    (hI : instantiate_eq_lam he = .under A₀ b₀ he₀ hAe hBe)
    (ih : LamVerdict inner σ (insertDisp .drop j ρ) (readLam hext Aw inner he₀)) :
    LamVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readLam hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readLam
  rw [hI]
  dsimp
  cases hri : readLam hext Aw inner he₀ with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushLamEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushLamEsub]
          exact .raw
      | star h =>
          simp only [pushLamEsub]
          refine .star ?_
          exact eps_esub_drop_star hu h
      | clause h =>
          simp only [pushLamEsub]
          refine .clause ?_
          simp only [lamClauseOf]
          exact esub_lam_drop_yes hext inner hget hv hvT g hAe hBe σ ρ hu h

def lamVerdict_esub_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body : Expr Nat} (he : instantiate j (lift 0 j repl) e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    {A₀ b₀ : Expr Nat} {he₀ : e = .lam A₀ b₀}
    {hAe : instantiate j (lift 0 j repl) A₀ = Al}
    {hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body}
    (hI : instantiate_eq_lam he = .under A₀ b₀ he₀ hAe hBe)
    (ih : LamVerdict inner σ (insertDisp .keep j ρ) (readLam hext Aw inner he₀)) :
    LamVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readLam hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readLam
  rw [hI]
  dsimp
  cases hri : readLam hext Aw inner he₀ with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushLamEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushLamEsub]
          exact .raw
      | star h =>
          simp only [pushLamEsub]
          refine .star ?_
          exact eps_esub_keep_star hu h
      | clause h =>
          cases hbit : levelIsZero (σ g.u) with
          | true =>
              simp only [pushLamEsub]
              refine .clause ?_
              simp only [lamClauseOf]
              exact esub_lam_keep_drop hext inner hget hv hvT g hAe hBe σ ρ hu
                hbit h
          | false =>
              by_cases hr : hv.eps σ ρ = .star
              · simp only [pushLamEsub]
                exact .raw
              · simp only [pushLamEsub]
                refine .clause ?_
                simp only [lamClauseOf]
                exact esub_lam_keep_keep hext inner hget hv hvT g hAe hBe σ ρ hu
                  hr hbit h

/-- `esub` of the variable. The reader returns the replacement. This walk
    does not claim its erasure: a bare proof `bvar` on `drop` is `★`
    (`eps_here_drop_bvar`), and `keep` is `eps_here_keep_hit` once the
    variable erases to `bvar (countKeep (ρ.take j))`. `cases` on a typing
    of `.bvar` does not eliminate `wk`. -/
def lamVerdict_here {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body : Expr Nat} (he : instantiate j (lift 0 j repl) e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    (hs : e = .bvar j) (hr : lift 0 j repl = .lam Al body)
    (hI : instantiate_eq_lam he = .here hs hr) :
    LamVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readLam hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readLam
  rw [hI]
  dsimp
  cases readLam hext Aw hv hr with
  | no =>
      simp only [LamRead.raise]
      exact .none
  | yes _ =>
      simp only [LamRead.raise]
      exact .raw

set_option maxHeartbeats 800000 in
def epsReadLam {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    (σ : Level → Level) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A body : Expr Nat} → (he : e = .lam A body) → (ρ : List Disp) →
    LamVerdict D σ ρ (readLam hext Aw D he)
  | _, _, _, _, .sort .., _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _ => by cases he
  | _, _, _, _, .pi .., _, _, he, _ => by cases he
  | n, Γ, _, _, .lam _ _ _ A₀ u body₀ B v hA hbody hB, A, body, he, ρ => by
      cases he
      exact lamVerdict_node hext Aw hA hbody hB σ ρ
  | _, _, _, _, .app .., _, _, he, _ => by cases he
  | _, _, _, _, .letE .., _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, he, ρ =>
      lamVerdict_conv hext Aw inner hc he σ ρ
        (epsReadLam hext Aw σ inner he ρ)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, ρ =>
      match hL : lift_eq_lam he with
      | .mk A₀ b₀ he₀ hAe hb₀ =>
          lamVerdict_wk hext Aw inner he σ ρ hL
            (epsReadLam hext Aw σ inner he₀ (removeAt ρ c))
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, ρ =>
      match hI : instantiate_eq_lam he with
      | .under A₀ b₀ he₀ hAe hBe =>
          match hu : levelIsZero (σ uE) with
          | true =>
              lamVerdict_esub_drop hext Aw inner hget hv hvT he σ ρ hu hI
                (epsReadLam hext Aw σ inner he₀ (insertDisp .drop j ρ))
          | false =>
              lamVerdict_esub_keep hext Aw inner hget hv hvT he σ ρ hu hI
                (epsReadLam hext Aw σ inner he₀ (insertDisp .keep j ρ))
      | .here hs hr =>
          lamVerdict_here hext Aw inner hget hv hvT he σ ρ hs hr hI
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, ρ =>
      match hL : instantiateLevels_eq_lam he with
      | .mk A₀ b₀ he₀ hAe hb₀ =>
          lamVerdict_linst hext Aw hls hlen inner he σ ρ hL
            (epsReadLam hext Aw (fun l => σ (instLevel ls l)) inner he₀ ρ)
  | _, _, _, _, .lsub .., _, _, _, _ => by
      unfold readLam
      exact .none
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he, ρ =>
      lamVerdict_ewk hext Aw hext' inner he σ ρ
        (epsReadLam (envExt_trans hext' hext) Aw σ inner he ρ)
  | _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA, _, _, he, ρ =>
      lamVerdict_cctx hext Aw D hA he σ ρ

/-! ## §6 a redex clause, transported

Same split of environments as §3. The argument is the got's `harg`,
weakened when the reader builds it from an application node. -/

theorem wk_redex_skip_ext {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {e T : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (hD : D.eps σ (removeAt ρ c) = redexClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
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
  rw [eps_wk_not_keep hk, hD]
  simp only [redexClauseOf]
  rw [hbody, harg]

theorem wk_redex_drop_ext {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {e T : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (removeAt ρ c) = redexClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ) := by
  simp only [hu, binderDisp, redexClauseOf] at hD ⊢
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

theorem wk_redex_keep_ext {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {e T : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hu : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (removeAt ρ c) = redexClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))).eps
          σ (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)).eps σ ρ) := by
  simp only [hu, binderDisp, redexClauseOf] at hD ⊢
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
        (g.hbody.eps σ (.keep :: removeAt ρ c)).lift
          (countKeep (ρ.take c) + 1) 1 := by
    rw [eps_tyCastCtx, eps_tyCast, eps_wk_keep hkB]
    simp only [removeAt, List.take_succ_cons, countKeep]
  rw [eps_wk_keep hk, hD, lift_redexClause_keep, hbody, harg]

theorem linst_redex_yes_ext {Em : ResolvedEnv} {a n : Nat} {Γ₀ : LCtx}
    {e T₀ : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D : TyP Em a Γ₀ e T₀)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E a Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
    (ha : instantiateLevels ls a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hD : D.eps (fun l => σ (instLevel ls l)) ρ =
      redexClauseOf g (fun l => σ (instLevel ls l)) ρ) :
    (TyP.linst Em a n Γ₀ e T₀ ls hls hlen D).eps σ ρ =
      redexClause (levelIsZero (σ (instLevel ls g.u)))
        ((tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
              (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
            (tyCast hb rfl
              (TyP.linst E a n (.assumption A₀ :: Γ₀) b₀ g.B ls hls hlen
                g.hbody))).eps
          σ (binderDisp (levelIsZero (σ (instLevel ls g.u))) :: ρ))
        ((tyCast ha rfl
            (TyP.linst E a n Γ₀ a₀ g.Aarg ls hls hlen g.harg)).eps σ ρ) := by
  rw [eps_linst]
  simp only [redexClauseOf] at hD ⊢
  rw [hD, eps_tyCastCtx, eps_tyCast, eps_linst, eps_tyCast, eps_linst]

theorem esub_redex_drop_ext {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    (hD : D.eps σ (insertDisp .drop j ρ) =
      redexClauseOf g σ (insertDisp .drop j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT)
            hAe hBe).eps σ
          (binderDisp (levelIsZero (σ g.u)) :: ρ))
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl)
                (lift 0 j t) hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ) := by
  have harg :
      (tyCast haEq rfl
          (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT))).eps σ ρ =
        g.harg.eps σ (insertDisp .drop j ρ) := by
    rw [eps_tyCast, eps_esub_drop (hu := hu)]
  have hbody :
      (pushBodyEsub g.hbody hget
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
            hext hv)
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
            hext hvT)
          hAe hBe).eps σ
        (binderDisp (levelIsZero (σ g.u)) :: ρ) =
        g.hbody.eps σ
          (binderDisp (levelIsZero (σ g.u)) :: insertDisp .drop j ρ) := by
    rw [eps_pushBody_drop _ _ _ _ _ _ _ (hu := hu)]
    rfl
  rw [eps_esub_drop (hu := hu), hD]
  simp only [redexClauseOf]
  rw [hbody, harg]

theorem esub_redex_keep_drop_ext {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false) (hr : hv.eps σ ρ ≠ .star)
    (hbit : levelIsZero (σ g.u) = true)
    (hD : D.eps σ (insertDisp .keep j ρ) =
      redexClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT)
            hAe hBe).eps σ (.drop :: ρ))
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl)
                (lift 0 j t) hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ) := by
  simp only [hbit, binderDisp, redexClauseOf] at hD ⊢
  have harg :
      (tyCast haEq rfl
          (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT))).eps σ ρ =
        ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (g.harg.eps σ (insertDisp .keep j ρ)) := by
    rw [eps_tyCast, eps_esub_keep (hu := hu)]
    rfl
  have hbody :
      (pushBodyEsub g.hbody hget
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
            hext hv)
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
            hext hvT)
          hAe hBe).eps σ (.drop :: ρ) =
        ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (g.hbody.eps σ (.drop :: insertDisp .keep j ρ)) := by
    rw [eps_pushBody_keep_drop _ _ _ _ _ _ _ _ hu]
    rfl
  rw [eps_esub_keep (hu := hu), hD, inst_redexClause_drop hr, hbody, harg]

theorem esub_redex_keep_keep_ext {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {A₀ b₀ a₀ : Expr Nat}
    (g : RedexGot Aw src E n Γ₀ A₀ b₀ a₀)
    {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false) (hr : hv.eps σ ρ ≠ .star)
    (hbit : levelIsZero (σ g.u) = false)
    (hD : D.eps σ (insertDisp .keep j ρ) =
      redexClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      redexClause (levelIsZero (σ g.u))
        ((pushBodyEsub g.hbody hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT)
            hAe hBe).eps σ (.keep :: ρ))
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl)
                (lift 0 j t) hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ) := by
  simp only [hbit, binderDisp, redexClauseOf] at hD ⊢
  have harg :
      (tyCast haEq rfl
          (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
              hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
              hext hvT))).eps σ ρ =
        ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (g.harg.eps σ (insertDisp .keep j ρ)) := by
    rw [eps_tyCast, eps_esub_keep (hu := hu)]
    rfl
  have hbody :
      (pushBodyEsub g.hbody hget
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
            hext hv)
          (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
            hext hvT)
          hAe hBe).eps σ (.keep :: ρ) =
        ETm.inst (countKeep (ρ.take j) + 1) ((hv.eps σ ρ).lift 0 1)
          (g.hbody.eps σ (.keep :: insertDisp .keep j ρ)) := by
    rw [eps_pushBody_keep_keep _ _ _ _ _ _ _ _ hu]
    rfl
  rw [eps_esub_keep (hu := hu), hD, inst_redexClause_keep hr, hbody, harg]

/-! ## §7 the redex walk -/

def redexVerdict_app {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {A body arg A₀ B₀ : Expr Nat}
    {w : Level}
    (hf : TyP Ei n Γ (.lam A body) (.pi A₀ B₀))
    (ha : TyP Ei n Γ arg A₀)
    (hT : TyP Ei n Γ (instantiate0 arg B₀) (.sort w))
    (σ : Level → Level) (ρ : List Disp)
    (ih : LamVerdict hf σ ρ (readLam hext Aw hf rfl)) :
    RedexVerdict (TyP.app Ei n Γ (.lam A body) arg A₀ B₀ w hf ha hT) σ ρ
      (readRedex hext Aw
        (TyP.app Ei n Γ (.lam A body) arg A₀ B₀ w hf ha hT) rfl) := by
  unfold readRedex
  dsimp
  cases hri : readLam hext Aw hf rfl with
  | no =>
      rw [hri] at ih
      cases ih
      exact .none
  | yes _ =>
      rw [hri] at ih
      cases ih with
      | raw =>
          exact .raw
      | star h =>
          refine .star ?_
          rw [eps_app_appClause, h]
          rfl
      | clause h =>
          refine .clause ?_
          rw [eps_app_appClause, h]
          simp only [lamClauseOf, redexClauseOf, redexClause]
          rfl

def redexVerdict_conv {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (inner : TyP Ei n Γ e A) (hc : CvP Ei n Γ A B (.sort u))
    {Al body arg : Expr Nat} (he : e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    (ih : RedexVerdict inner σ ρ (readRedex hext Aw inner he)) :
    RedexVerdict (TyP.conv Ei n Γ e A B u inner hc) σ ρ
      (readRedex hext Aw (TyP.conv Ei n Γ e A B u inner hc) he) := by
  unfold readRedex
  cases hri : readRedex hext Aw inner he with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [RedexRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [RedexRead.raise]
          exact .raw
      | star h =>
          simp only [RedexRead.raise]
          refine .star ?_
          rw [eps_conv, h]
      | clause h =>
          simp only [RedexRead.raise]
          refine .clause ?_
          rw [eps_conv, h]
          rfl

def redexVerdict_ewk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (hext' : EnvExt E₀ Ei) (inner : TyP E₀ n Γ e A)
    {Al body arg : Expr Nat} (he : e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    (ih : RedexVerdict inner σ ρ
      (readRedex (envExt_trans hext' hext) Aw inner he)) :
    RedexVerdict (TyP.ewk E₀ Ei n Γ e A hext' inner) σ ρ
      (readRedex hext Aw (TyP.ewk E₀ Ei n Γ e A hext' inner) he) := by
  unfold readRedex
  cases hri : readRedex (envExt_trans hext' hext) Aw inner he with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [RedexRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [RedexRead.raise]
          exact .raw
      | star h =>
          simp only [RedexRead.raise]
          refine .star ?_
          rw [eps_ewk, h]
      | clause h =>
          simp only [RedexRead.raise]
          refine .clause ?_
          rw [eps_ewk, h]
          rfl

def redexVerdict_cctx {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u : Level}
    (D : TyP Ei n (.assumption A :: Γ) e T) (hA : CvP Ei n Γ A A' (.sort u))
    {Al body arg : Expr Nat} (he : e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp) :
    RedexVerdict (TyP.cctx Ei n Γ e T A A' u D hA) σ ρ
      (readRedex hext Aw (TyP.cctx Ei n Γ e T A A' u D hA) he) := by
  unfold readRedex
  exact .none

def redexVerdict_wk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d : LocalDecl} {c : Nat} (inner : TyP Ei n Γ₀ e₀ T₀)
    {Al body arg : Expr Nat} (he : lift c 1 e₀ = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    {f₀ a₀ : Expr Nat} {he₀ : e₀ = .app f₀ a₀}
    {hf₀ : lift c 1 f₀ = .lam Al body} {ha₀ : lift c 1 a₀ = arg}
    (hF : lift_eq_app he = .mk f₀ a₀ he₀ hf₀ ha₀)
    {A₀ b₀ : Expr Nat} {heLam : f₀ = .lam A₀ b₀}
    {hAe : lift c 1 A₀ = Al} {hb₀ : lift (c + 1) 1 b₀ = body}
    (hL : lift_eq_lam hf₀ = .mk A₀ b₀ heLam hAe hb₀)
    (ih : RedexVerdict inner σ (removeAt ρ c)
      (readRedex hext Aw inner (app_of_lam he₀ heLam))) :
    RedexVerdict (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) σ ρ
      (readRedex hext Aw (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) he) := by
  unfold readRedex
  rw [hF]
  dsimp
  rw [hL]
  dsimp
  cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushRedexWk, RedexRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushRedexWk, RedexRead.raise]
          exact .raw
      | star h =>
          simp only [pushRedexWk, RedexRead.raise]
          refine .star ?_
          exact eps_wk_star h
      | clause h =>
          simp only [pushRedexWk, RedexRead.raise]
          refine .clause ?_
          simp only [redexClauseOf]
          cases hρ : ρ[c]? with
          | none =>
              exact wk_redex_skip_ext inner g hAe hb₀ ha₀ σ ρ (Or.inl hρ) h
          | some disp =>
              cases disp with
              | drop =>
                  exact wk_redex_skip_ext inner g hAe hb₀ ha₀ σ ρ
                    (Or.inr (Or.inl hρ)) h
              | inline v =>
                  exact wk_redex_skip_ext inner g hAe hb₀ ha₀ σ ρ
                    (Or.inr (Or.inr ⟨v, hρ⟩)) h
              | keep =>
                  cases hu : levelIsZero (σ g.u) with
                  | true =>
                      simpa [hu, binderDisp] using
                        wk_redex_drop_ext inner g hAe hb₀ ha₀ σ ρ hρ hu h
                  | false =>
                      simpa [hu, binderDisp] using
                        wk_redex_keep_ext inner g hAe hb₀ ha₀ σ ρ hρ hu h

def redexVerdict_linst {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {a n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {ls : List Level} (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (inner : TyP Ei a Γ₀ e₀ T₀)
    {Al body arg : Expr Nat}
    (he : instantiateLevels ls e₀ = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    {f₀ a₀ : Expr Nat} {he₀ : e₀ = .app f₀ a₀}
    {hf₀ : instantiateLevels ls f₀ = .lam Al body}
    {ha₀ : instantiateLevels ls a₀ = arg}
    (hF : instantiateLevels_eq_app he = .mk f₀ a₀ he₀ hf₀ ha₀)
    {A₀ b₀ : Expr Nat} {heLam : f₀ = .lam A₀ b₀}
    {hAe : instantiateLevels ls A₀ = Al}
    {hb₀ : instantiateLevels ls b₀ = body}
    (hL : instantiateLevels_eq_lam hf₀ = .mk A₀ b₀ heLam hAe hb₀)
    (ih : RedexVerdict inner (fun l => σ (instLevel ls l)) ρ
      (readRedex hext Aw inner (app_of_lam he₀ heLam))) :
    RedexVerdict (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) σ ρ
      (readRedex hext Aw (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) he) := by
  unfold readRedex
  rw [hF]
  dsimp
  rw [hL]
  dsimp
  cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushRedexLinst, RedexRead.raise]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushRedexLinst, RedexRead.raise]
          exact .raw
      | star h =>
          simp only [pushRedexLinst, RedexRead.raise]
          refine .star ?_
          exact eps_linst_star h
      | clause h =>
          simp only [pushRedexLinst, RedexRead.raise]
          refine .clause ?_
          simp only [redexClauseOf]
          exact linst_redex_yes_ext hls hlen inner g hAe hb₀ ha₀ σ ρ h

def redexVerdict_esub_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body arg : Expr Nat}
    (he : instantiate j (lift 0 j repl) e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    {f₀ a₀ : Expr Nat} {he₀ : e = .app f₀ a₀}
    {hf₀ : instantiate j (lift 0 j repl) f₀ = .lam Al body}
    {ha₀ : instantiate j (lift 0 j repl) a₀ = arg}
    (hF : instantiate_eq_app he = .under f₀ a₀ he₀ hf₀ ha₀)
    {A₀ b₀ : Expr Nat} {heLam : f₀ = .lam A₀ b₀}
    {hAe : instantiate j (lift 0 j repl) A₀ = Al}
    {hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body}
    (hL : instantiate_eq_lam hf₀ = .under A₀ b₀ heLam hAe hBe)
    (ih : RedexVerdict inner σ (insertDisp .drop j ρ)
      (readRedex hext Aw inner (app_of_lam he₀ heLam))) :
    RedexVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readRedex hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readRedex
  rw [hF]
  dsimp
  rw [hL]
  dsimp
  cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushRedexEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushRedexEsub]
          exact .raw
      | star h =>
          simp only [pushRedexEsub]
          refine .star ?_
          exact eps_esub_drop_star hu h
      | clause h =>
          simp only [pushRedexEsub]
          refine .clause ?_
          simp only [redexClauseOf]
          exact esub_redex_drop_ext hext inner hget hv hvT g hAe hBe ha₀ σ ρ hu h

def redexVerdict_esub_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body arg : Expr Nat}
    (he : instantiate j (lift 0 j repl) e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    {f₀ a₀ : Expr Nat} {he₀ : e = .app f₀ a₀}
    {hf₀ : instantiate j (lift 0 j repl) f₀ = .lam Al body}
    {ha₀ : instantiate j (lift 0 j repl) a₀ = arg}
    (hF : instantiate_eq_app he = .under f₀ a₀ he₀ hf₀ ha₀)
    {A₀ b₀ : Expr Nat} {heLam : f₀ = .lam A₀ b₀}
    {hAe : instantiate j (lift 0 j repl) A₀ = Al}
    {hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body}
    (hL : instantiate_eq_lam hf₀ = .under A₀ b₀ heLam hAe hBe)
    (ih : RedexVerdict inner σ (insertDisp .keep j ρ)
      (readRedex hext Aw inner (app_of_lam he₀ heLam))) :
    RedexVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readRedex hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readRedex
  rw [hF]
  dsimp
  rw [hL]
  dsimp
  cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushRedexEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushRedexEsub]
          exact .raw
      | star h =>
          simp only [pushRedexEsub]
          refine .star ?_
          exact eps_esub_keep_star hu h
      | clause h =>
          cases hbit : levelIsZero (σ g.u) with
          | true =>
              by_cases hr : hv.eps σ ρ = .star
              · simp only [pushRedexEsub]
                exact .raw
              · simp only [pushRedexEsub]
                refine .clause ?_
                simpa [redexClauseOf, hbit, binderDisp] using
                  esub_redex_keep_drop_ext hext inner hget hv hvT g hAe hBe
                    ha₀ σ ρ hu hr hbit h
          | false =>
              by_cases hr : hv.eps σ ρ = .star
              · simp only [pushRedexEsub]
                exact .raw
              · simp only [pushRedexEsub]
                refine .clause ?_
                simpa [redexClauseOf, hbit, binderDisp] using
                  esub_redex_keep_keep_ext hext inner hget hv hvT g hAe hBe
                    ha₀ σ ρ hu hr hbit h

/-- An application whose function is the substituted variable is not a
    redex this reader pushes. -/
def redexVerdict_born {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body arg : Expr Nat}
    (he : instantiate j (lift 0 j repl) e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    {f₀ a₀ : Expr Nat} {he₀ : e = .app f₀ a₀}
    {hf₀ : instantiate j (lift 0 j repl) f₀ = .lam Al body}
    {ha₀ : instantiate j (lift 0 j repl) a₀ = arg}
    (hF : instantiate_eq_app he = .under f₀ a₀ he₀ hf₀ ha₀)
    (hs : f₀ = .bvar j) (hr : lift 0 j repl = .lam Al body)
    (hL : instantiate_eq_lam hf₀ = .here hs hr) :
    RedexVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readRedex hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readRedex
  rw [hF]
  simp only [hL]
  exact .none

def redexVerdict_here {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body arg : Expr Nat}
    (he : instantiate j (lift 0 j repl) e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    (hs : e = .bvar j) (hr : lift 0 j repl = .app (.lam Al body) arg)
    (hI : instantiate_eq_app he = .here hs hr) :
    RedexVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readRedex hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readRedex
  rw [hI]
  dsimp
  cases readRedex hext Aw hv hr with
  | no =>
      simp only [RedexRead.raise]
      exact .none
  | yes _ =>
      simp only [RedexRead.raise]
      exact .raw

set_option maxHeartbeats 800000 in
def epsReadRedex {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    (σ : Level → Level) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A body arg : Expr Nat} → (he : e = .app (.lam A body) arg) →
    (ρ : List Disp) →
    RedexVerdict D σ ρ (readRedex hext Aw D he)
  | _, _, _, _, .sort .., _, _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, _, he, _ => by cases he
  | _, _, _, _, .pi .., _, _, _, he, _ => by cases he
  | _, _, _, _, .lam .., _, _, _, he, _ => by cases he
  | _, _, _, _, .app _ _ _ f a A₀ B₀ w hf ha hT, A, body, arg, he, ρ =>
      match f, a, he with
      | _, _, rfl =>
          redexVerdict_app hext Aw hf ha hT σ ρ
            (epsReadLam hext Aw σ hf rfl ρ)
  | _, _, _, _, .letE .., _, _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, _, he, ρ =>
      redexVerdict_conv hext Aw inner hc he σ ρ
        (epsReadRedex hext Aw σ inner he ρ)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, _, he, ρ =>
      match hF : lift_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          match hL : lift_eq_lam hf₀ with
          | .mk A₀ b₀ heLam hAe hb₀ =>
              redexVerdict_wk hext Aw inner he σ ρ hF hL
                (epsReadRedex hext Aw σ inner (app_of_lam he₀ heLam)
                  (removeAt ρ c))
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, _, he, ρ =>
      match hF : instantiate_eq_app he with
      | .under f₀ a₀ he₀ hf₀ ha₀ =>
          match hL : instantiate_eq_lam hf₀ with
          | .under A₀ b₀ heLam hAe hBe =>
              match hu : levelIsZero (σ uE) with
              | true =>
                  redexVerdict_esub_drop hext Aw inner hget hv hvT he σ ρ hu
                    hF hL
                    (epsReadRedex hext Aw σ inner (app_of_lam he₀ heLam)
                      (insertDisp .drop j ρ))
              | false =>
                  redexVerdict_esub_keep hext Aw inner hget hv hvT he σ ρ hu
                    hF hL
                    (epsReadRedex hext Aw σ inner (app_of_lam he₀ heLam)
                      (insertDisp .keep j ρ))
          | .here hs hr =>
              redexVerdict_born hext Aw inner hget hv hvT he σ ρ hF hs hr hL
      | .here hs hr =>
          redexVerdict_here hext Aw inner hget hv hvT he σ ρ hs hr hF
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, _, he, ρ =>
      match hF : instantiateLevels_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          match hL : instantiateLevels_eq_lam hf₀ with
          | .mk A₀ b₀ heLam hAe hb₀ =>
              redexVerdict_linst hext Aw hls hlen inner he σ ρ hF hL
                (epsReadRedex hext Aw (fun l => σ (instLevel ls l)) inner
                  (app_of_lam he₀ heLam) ρ)
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, _, he, ρ =>
      redexVerdict_ewk hext Aw hext' inner he σ ρ
        (epsReadRedex (envExt_trans hext' hext) Aw σ inner he ρ)
  | _, _, _, _, .lsub .., _, _, _, _, _ => by
      unfold readRedex
      exact .none
  | _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA, _, _, _, he, ρ =>
      redexVerdict_cctx hext Aw D hA he σ ρ

end Rcic.Syn

#print axioms Rcic.Syn.eps_wk_star
#print axioms Rcic.Syn.eps_linst_star
#print axioms Rcic.Syn.eps_esub_drop_star
#print axioms Rcic.Syn.eps_esub_keep_star
#print axioms Rcic.Syn.wk_lam_skip
#print axioms Rcic.Syn.wk_lam_drop
#print axioms Rcic.Syn.wk_lam_keep
#print axioms Rcic.Syn.linst_lam_yes
#print axioms Rcic.Syn.esub_lam_drop_yes
#print axioms Rcic.Syn.esub_lam_keep_drop
#print axioms Rcic.Syn.esub_lam_keep_keep
#print axioms Rcic.Syn.eps_here_drop_bvar
#print axioms Rcic.Syn.eps_here_keep_hit
#print axioms Rcic.Syn.eps_here_keep_hit_redex
#print axioms Rcic.Syn.lamVerdict_node
#print axioms Rcic.Syn.lamVerdict_conv
#print axioms Rcic.Syn.lamVerdict_ewk
#print axioms Rcic.Syn.lamVerdict_cctx
#print axioms Rcic.Syn.lamVerdict_wk
#print axioms Rcic.Syn.lamVerdict_linst
#print axioms Rcic.Syn.lamVerdict_esub_drop
#print axioms Rcic.Syn.lamVerdict_esub_keep
#print axioms Rcic.Syn.lamVerdict_here
#print axioms Rcic.Syn.epsReadLam
#print axioms Rcic.Syn.wk_redex_skip_ext
#print axioms Rcic.Syn.wk_redex_drop_ext
#print axioms Rcic.Syn.wk_redex_keep_ext
#print axioms Rcic.Syn.linst_redex_yes_ext
#print axioms Rcic.Syn.esub_redex_drop_ext
#print axioms Rcic.Syn.esub_redex_keep_drop_ext
#print axioms Rcic.Syn.esub_redex_keep_keep_ext
#print axioms Rcic.Syn.redexVerdict_app
#print axioms Rcic.Syn.redexVerdict_conv
#print axioms Rcic.Syn.redexVerdict_ewk
#print axioms Rcic.Syn.redexVerdict_cctx
#print axioms Rcic.Syn.redexVerdict_wk
#print axioms Rcic.Syn.redexVerdict_linst
#print axioms Rcic.Syn.redexVerdict_esub_drop
#print axioms Rcic.Syn.redexVerdict_esub_keep
#print axioms Rcic.Syn.redexVerdict_born
#print axioms Rcic.Syn.redexVerdict_here
#print axioms Rcic.Syn.epsReadRedex
