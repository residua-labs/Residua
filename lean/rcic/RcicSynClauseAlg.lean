import rcic.RcicSynRedex

/-!
# Syntactic sortRow, build step 3x — the erasure clause commutes

`research/rcic/semantic/S3_ES_ARMS.md` §23. `TyP.eps` of an application is a
nested match. `appClause` is that clause as a function of two erased terms.
A simultaneous match on the pair is a different matcher: `simp [appClause]`
unfolds it to a match that does not reduce on constructors. `appClause_cases`
bridges the two by `cases` on both terms and `rfl`, with the clause left
folded.

`lift` and `inst` commute with `appClause`, `lamClause` and `redexClause`.
The bvar `if` inside `lift` / `inst` is split in `lift_eq_star` and
`inst_eq_star`, after `cases` on the term, so the scrutinee is a constructor.
`inst` needs `r ≠ ★`. `app (bvar j) t` with a non-`★` `t` instantiates at `★`
to `app ★ _`, and the clause of that is `★` (`inst_appClause_star_ne`).

`eps_beta_node` is the pure `app` of a pure `lam`: its erasure is
`redexClause` of the body and the argument. `wk`, `esub`, `linst`, `conv`,
`ewk` and `cctx` transport a clause that is already the inner erasure.
`cctx` still returns `.no` from `readRedex` (the atom bound). An `esub` on
the `drop` path erases the variable to `★` (`resolve_insertDisp_drop`); that
spine is not one of these transports. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the clauses -/

/-- Delete a `★` function, else delete a `★` argument, else keep the application.
    Nested, so it is the matcher `TyP.eps` uses for `.app`. -/
def appClause (ef ea : ETm) : ETm :=
  match ef with
  | .star => .star
  | ef =>
    match ea with
    | .star => ef
    | ea => .app ef ea

/-- Delete a `★` body; otherwise keep the `λ`. The domain is already gone. -/
def lamClause : ETm → ETm
  | .star => .star
  | eb => .lam eb

/-- Proof domain: the `λ` is gone, and `eb` is the body. Relevant domain: `lamClause`. -/
def lamErasure (proofDom : Bool) (eb : ETm) : ETm :=
  match proofDom with
  | true => eb
  | false => lamClause eb

/-- `app (lam …) arg`, after the domain bit has chosen whether the `λ` survives. -/
def redexClause (proofDom : Bool) (eb ea : ETm) : ETm :=
  appClause (lamErasure proofDom eb) ea

theorem appClause_right_star (ef : ETm) : appClause ef .star = ef := by
  cases ef <;> rfl

theorem appClause_app {ef ea : ETm} (hf : ef ≠ .star) (ha : ea ≠ .star) :
    appClause ef ea = .app ef ea := by
  cases ef <;> cases ea <;> first | rfl | exact absurd rfl hf | exact absurd rfl ha

/-- The nested clause and the simultaneous match agree on constructors. -/
theorem appClause_cases (ef ea : ETm) :
    appClause ef ea =
      match ef, ea with
      | .star, _ => .star
      | _, .star => ef
      | ef, ea => .app ef ea := by
  cases ef <;> cases ea <;> rfl

theorem lamClause_of_ne {eb : ETm} (h : eb ≠ .star) : lamClause eb = .lam eb := by
  cases eb <;> first | rfl | exact absurd rfl h

/-! ## §2 `★` is closed under `lift` and, off a `★` replacement, under `inst` -/

theorem lift_eq_star {c k : Nat} {t : ETm} (h : t.lift c k = .star) : t = .star := by
  cases t <;> simp only [ETm.lift] at h <;> first | rfl | (split at h <;> nomatch h) | nomatch h

theorem inst_eq_star {j : Nat} {r t : ETm} (hr : r ≠ .star) (h : ETm.inst j r t = .star) :
    t = .star := by
  cases t with
  | bvar i =>
    simp only [ETm.inst] at h
    split at h
    · exact absurd h hr
    · split at h <;> nomatch h
  | star => rfl
  | sort _ =>
    simp only [ETm.inst] at h
    nomatch h
  | const _ _ =>
    simp only [ETm.inst] at h
    nomatch h
  | app _ _ =>
    simp only [ETm.inst] at h
    nomatch h
  | lam _ =>
    simp only [ETm.inst] at h
    nomatch h
  | pi _ _ =>
    simp only [ETm.inst] at h
    nomatch h

theorem lift_ne_star {c k : Nat} {t : ETm} (ht : t ≠ .star) : t.lift c k ≠ .star :=
  fun h => ht (lift_eq_star h)

theorem inst_ne_star {j : Nat} {r t : ETm} (hr : r ≠ .star) (ht : t ≠ .star) :
    ETm.inst j r t ≠ .star :=
  fun h => ht (inst_eq_star hr h)

/-! ## §3 commutation -/

theorem lift_appClause (c k : Nat) (ef ea : ETm) :
    (appClause ef ea).lift c k = appClause (ef.lift c k) (ea.lift c k) := by
  by_cases hea : ea = .star
  · cases hea
    simp only [ETm.lift]
    rw [appClause_right_star, appClause_right_star]
  · by_cases hef : ef = .star
    · cases hef
      rfl
    · rw [appClause_app hef hea]
      have hL : (ETm.app ef ea).lift c k = .app (ef.lift c k) (ea.lift c k) := rfl
      rw [hL, appClause_app (lift_ne_star hef) (lift_ne_star hea)]

theorem lift_lamClause (c k : Nat) (eb : ETm) :
    (lamClause eb).lift c k = lamClause (eb.lift (c + 1) k) := by
  by_cases h : eb = .star
  · cases h
    rfl
  · rw [lamClause_of_ne h]
    have hL : (ETm.lam eb).lift c k = .lam (eb.lift (c + 1) k) := rfl
    rw [hL, lamClause_of_ne (lift_ne_star h)]

theorem inst_appClause_right_star (j : Nat) (r ef : ETm) :
    ETm.inst j r (appClause ef .star) = appClause (ETm.inst j r ef) .star := by
  rw [appClause_right_star, appClause_right_star]

theorem inst_appClause_both (j : Nat) {r ef ea : ETm}
    (hr : r ≠ .star) (hf : ef ≠ .star) (ha : ea ≠ .star) :
    ETm.inst j r (appClause ef ea) =
      appClause (ETm.inst j r ef) (ETm.inst j r ea) := by
  rw [appClause_app hf ha]
  have hL : ETm.inst j r (.app ef ea) = .app (ETm.inst j r ef) (ETm.inst j r ea) := rfl
  rw [hL, appClause_app (inst_ne_star hr hf) (inst_ne_star hr ha)]

theorem inst_appClause (j : Nat) {r : ETm} (hr : r ≠ .star) (ef ea : ETm) :
    ETm.inst j r (appClause ef ea) =
      appClause (ETm.inst j r ef) (ETm.inst j r ea) := by
  by_cases hea : ea = .star
  · cases hea
    rw [show ETm.inst j r .star = .star from rfl]
    exact inst_appClause_right_star j r ef
  · by_cases hef : ef = .star
    · cases hef
      rfl
    · exact inst_appClause_both j hr hef hea

theorem inst_lamClause (j : Nat) {r : ETm} (hr : r ≠ .star) (eb : ETm) :
    ETm.inst j r (lamClause eb) =
      lamClause (ETm.inst (j + 1) (r.lift 0 1) eb) := by
  by_cases h : eb = .star
  · cases h
    rfl
  · rw [lamClause_of_ne h]
    have hL : ETm.inst j r (.lam eb) = .lam (ETm.inst (j + 1) (r.lift 0 1) eb) := rfl
    rw [hL, lamClause_of_ne (inst_ne_star (lift_ne_star hr) h)]

/-- The clause does not survive a `★` replacement. `inst` produces `app ★ _`;
    the clause of a `★` function is `★`. -/
theorem inst_appClause_star_ne (j : Nat) (t : ETm) (ht : t ≠ .star) :
    ETm.inst j .star (appClause (.bvar j) t) ≠
      appClause (ETm.inst j .star (.bvar j)) (ETm.inst j .star t) := by
  have hb : ETm.bvar j ≠ .star := by
    intro h
    cases h
  rw [appClause_app hb ht]
  have hL : ETm.inst j .star (.app (.bvar j) t) =
      .app (ETm.inst j .star (.bvar j)) (ETm.inst j .star t) := rfl
  rw [hL, inst_bvar_hit]
  simp only [appClause]
  intro h
  cases h

theorem lift_redexClause_drop (eb ea : ETm) (c k : Nat) :
    (redexClause true eb ea).lift c k =
      redexClause true (eb.lift c k) (ea.lift c k) := by
  simp only [redexClause, lamErasure]
  exact lift_appClause c k eb ea

theorem lift_redexClause_keep (eb ea : ETm) (c k : Nat) :
    (redexClause false eb ea).lift c k =
      redexClause false (eb.lift (c + 1) k) (ea.lift c k) := by
  simp only [redexClause, lamErasure]
  rw [lift_appClause, lift_lamClause]

theorem inst_redexClause_drop {r : ETm} (hr : r ≠ .star) (j : Nat) (eb ea : ETm) :
    ETm.inst j r (redexClause true eb ea) =
      redexClause true (ETm.inst j r eb) (ETm.inst j r ea) := by
  simp only [redexClause, lamErasure]
  exact inst_appClause j hr eb ea

theorem inst_redexClause_keep {r : ETm} (hr : r ≠ .star) (j : Nat) (eb ea : ETm) :
    ETm.inst j r (redexClause false eb ea) =
      redexClause false
        (ETm.inst (j + 1) (r.lift 0 1) eb) (ETm.inst j r ea) := by
  simp only [redexClause, lamErasure]
  rw [inst_appClause j hr, inst_lamClause j hr]

/-! ## §4 the pure redex, and transporting a clause -/

theorem eps_app_appClause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.app E n Γ f a A B w hf ha hT).eps σ ρ =
      appClause (hf.eps σ ρ) (ha.eps σ ρ) := by
  cases h1 : hf.eps σ ρ <;> cases h2 : ha.eps σ ρ <;> simp only [TyP.eps, h1, h2] <;> rfl

theorem eps_lam_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.lam E n Γ A u body B v hA hbody hB).eps σ ρ =
      lamErasure (levelIsZero (σ u))
        (hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) := by
  cases hu : levelIsZero (σ u)
  case true =>
    simp only [TyP.eps, lamErasure, binderDisp, hu]
  case false =>
    simp only [TyP.eps, lamErasure, binderDisp, hu]
    cases hb : hbody.eps σ (.keep :: ρ) <;> simp only [lamClause, hb]

theorem eps_beta_node {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    {arg : Expr Nat} {w : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (ha : TyP E n Γ arg A)
    (hT : TyP E n Γ (instantiate0 arg B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.app E n Γ (.lam A body) arg A B w
        (TyP.lam E n Γ A u body B v hA hbody hB) ha hT).eps σ ρ =
      redexClause (levelIsZero (σ u))
        (hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))
        (ha.eps σ ρ) := by
  rw [eps_app_appClause, eps_lam_clause]
  rfl

theorem eps_conv_redex {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level} {h : TyP E n Γ e A}
    {hc : CvP E n Γ A B (.sort u)} {σ : Level → Level} {ρ : List Disp}
    {proofDom : Bool} {eb ea : ETm}
    (hD : h.eps σ ρ = redexClause proofDom eb ea) :
    (TyP.conv E n Γ e A B u h hc).eps σ ρ = redexClause proofDom eb ea := by
  rw [eps_conv, hD]

theorem eps_ewk_redex {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {hext : EnvExt E₀ E} {D : TyP E₀ n Γ e A} {σ : Level → Level} {ρ : List Disp}
    {proofDom : Bool} {eb ea : ETm}
    (hD : D.eps σ ρ = redexClause proofDom eb ea) :
    (TyP.ewk E₀ E n Γ e A hext D).eps σ ρ = redexClause proofDom eb ea := by
  rw [eps_ewk, hD]

theorem eps_cctx_redex {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A A' : Expr Nat} {u : Level}
    {D : TyP E n (.assumption A :: Γ) e T} {hA : CvP E n Γ A A' (.sort u)}
    {σ : Level → Level} {ρ : List Disp} {proofDom : Bool} {eb ea : ETm}
    (hD : D.eps σ ρ = redexClause proofDom eb ea) :
    (TyP.cctx E n Γ e T A A' u D hA).eps σ ρ = redexClause proofDom eb ea := by
  rw [eps_cctx, hD]

theorem eps_linst_redex {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {ls : List Level} {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    {D : TyP E a Γ e A} {σ : Level → Level} {ρ : List Disp}
    {proofDom : Bool} {eb ea : ETm}
    (hD : D.eps (fun l => σ (instLevel ls l)) ρ = redexClause proofDom eb ea) :
    (TyP.linst E a n Γ e A ls hls hlen D).eps σ ρ = redexClause proofDom eb ea := by
  rw [eps_linst, hD]

theorem eps_wk_redex_skip {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    {proofDom : Bool} {eb ea : ETm}
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (hD : D.eps σ (removeAt ρ c) = redexClause proofDom eb ea) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = redexClause proofDom eb ea := by
  rw [eps_wk_not_keep hk, hD]

theorem eps_wk_redex_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    {eb ea : ETm} (hk : ρ[c]? = some .keep)
    (hD : D.eps σ (removeAt ρ c) = redexClause true eb ea) :
    (TyP.wk E n Γ e A d c D).eps σ ρ =
      redexClause true
        (eb.lift (countKeep (ρ.take c)) 1)
        (ea.lift (countKeep (ρ.take c)) 1) := by
  rw [eps_wk_keep hk, hD, lift_redexClause_drop]

theorem eps_wk_redex_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    {eb ea : ETm} (hk : ρ[c]? = some .keep)
    (hD : D.eps σ (removeAt ρ c) = redexClause false eb ea) :
    (TyP.wk E n Γ e A d c D).eps σ ρ =
      redexClause false
        (eb.lift (countKeep (ρ.take c) + 1) 1)
        (ea.lift (countKeep (ρ.take c)) 1) := by
  rw [eps_wk_keep hk, hD, lift_redexClause_keep]

theorem eps_esub_redex_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} {proofDom : Bool} {eb ea : ETm}
    (hu : levelIsZero (σ u) = true)
    (hD : D.eps σ (insertDisp .drop j ρ) = redexClause proofDom eb ea) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      redexClause proofDom eb ea := by
  rw [eps_esub_drop (hu := hu), hD]

theorem eps_esub_redex_keep_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} {eb ea : ETm}
    (hu : levelIsZero (σ u) = false) (hr : hv.eps σ ρ ≠ .star)
    (hD : D.eps σ (insertDisp .keep j ρ) = redexClause true eb ea) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      redexClause true
        (ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ) eb)
        (ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ) ea) := by
  rw [eps_esub_keep (hu := hu), hD, inst_redexClause_drop hr]

theorem eps_esub_redex_keep_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} {eb ea : ETm}
    (hu : levelIsZero (σ u) = false) (hr : hv.eps σ ρ ≠ .star)
    (hD : D.eps σ (insertDisp .keep j ρ) = redexClause false eb ea) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      redexClause false
        (ETm.inst (countKeep (ρ.take j) + 1) ((hv.eps σ ρ).lift 0 1) eb)
        (ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ) ea) := by
  rw [eps_esub_keep (hu := hu), hD, inst_redexClause_keep hr]

end Rcic.Syn

#print axioms Rcic.Syn.binderDisp_drop
#print axioms Rcic.Syn.binderDisp_keep
#print axioms Rcic.Syn.appClause_right_star
#print axioms Rcic.Syn.appClause_app
#print axioms Rcic.Syn.appClause_cases
#print axioms Rcic.Syn.lamClause_of_ne
#print axioms Rcic.Syn.lift_eq_star
#print axioms Rcic.Syn.inst_eq_star
#print axioms Rcic.Syn.lift_ne_star
#print axioms Rcic.Syn.inst_ne_star
#print axioms Rcic.Syn.lift_appClause
#print axioms Rcic.Syn.lift_lamClause
#print axioms Rcic.Syn.inst_appClause_right_star
#print axioms Rcic.Syn.inst_appClause_both
#print axioms Rcic.Syn.inst_appClause
#print axioms Rcic.Syn.inst_lamClause
#print axioms Rcic.Syn.inst_appClause_star_ne
#print axioms Rcic.Syn.lift_redexClause_drop
#print axioms Rcic.Syn.lift_redexClause_keep
#print axioms Rcic.Syn.inst_redexClause_drop
#print axioms Rcic.Syn.inst_redexClause_keep
#print axioms Rcic.Syn.eps_app_appClause
#print axioms Rcic.Syn.eps_lam_clause
#print axioms Rcic.Syn.eps_beta_node
#print axioms Rcic.Syn.eps_conv_redex
#print axioms Rcic.Syn.eps_ewk_redex
#print axioms Rcic.Syn.eps_cctx_redex
#print axioms Rcic.Syn.eps_linst_redex
#print axioms Rcic.Syn.eps_wk_redex_skip
#print axioms Rcic.Syn.eps_wk_redex_drop
#print axioms Rcic.Syn.eps_wk_redex_keep
#print axioms Rcic.Syn.eps_esub_redex_drop
#print axioms Rcic.Syn.eps_esub_redex_keep_drop
#print axioms Rcic.Syn.eps_esub_redex_keep_keep
