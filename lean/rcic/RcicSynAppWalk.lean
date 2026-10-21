import rcic.RcicSynEtaBody
import rcic.RcicSynBvarHere

/-!
# Syntactic sortRow, build step 3ak — the erasure walk of an application reading

`research/rcic/semantic/S3_ES_ARMS.md` §36. `readApp` (§30) walks a typing of
`.app f arg` and returns a typing of the function and of the argument, both
under an external atom bound `src`. Nothing said what the walked derivation
erases to. `epsWalkApp` is that walk, in the shape of `epsWalkLam`.

`AppVerdict` records which claim holds:

- `clause`: the derivation erases to `appClause` of the got's two erasures
  (`appClauseOf`);
- `star`: it erases to `★`, and that is not claimed to be the got's clause;
- `raw`: the reader returned `.yes` and this walk does not claim the erasure;
- `none`: the reader returned `.no` (`cctx`, `lsub`).

The application node is `clause` by `eps_app_appClause`. `conv` and `ewk`
keep the erasure (`AppVerdict.move`). `wk` lifts the clause on a `keep`
(`lift_appClause`) and leaves it on any other disposition. `linst`
recomputes `σ`. `esub` on `drop` leaves the clause. `esub` on `keep` is
`inst_appClause` when the replacement does not erase to `★`; a `★`
replacement stays `raw` (`inst_appClause_star_ne` is the counterexample to
the clause there). `esub`-here is `bareHere`: a proof variable on either
path is `star`, and an in-range relevant variable on `keep` hits, so the
replacement's verdict is the outer verdict.

Unlike `readLam`, the reader does not raise its bound, so a got is the same
object on every spine that does not push it.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 what an application got erases to -/

def appClauseOf {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f arg : Expr Nat} (g : AppGot Aw src E n Γ f arg)
    (σ : Level → Level) (ρ : List Disp) : ETm :=
  appClause (g.hf.eps σ ρ) (g.ha.eps σ ρ)

/-- Erasure of `D` against the reading of an application. `raw` is a `.yes`
    the walk does not identify. -/
inductive AppVerdict {Ei : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP Ei n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    {Aw : Nat → Nat} → {src : Nat} → {E : ResolvedEnv} → {f arg : Expr Nat} →
    AppRead Aw src E n Γ f arg → Type where
  | clause {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {f arg : Expr Nat}
      {g : AppGot Aw src E n Γ f arg}
      (h : D.eps σ ρ = appClauseOf g σ ρ) : AppVerdict D σ ρ (.yes g)
  | star {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {f arg : Expr Nat}
      {g : AppGot Aw src E n Γ f arg}
      (h : D.eps σ ρ = .star) : AppVerdict D σ ρ (.yes g)
  | raw {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {f arg : Expr Nat}
      {g : AppGot Aw src E n Γ f arg} : AppVerdict D σ ρ (.yes g)
  | none {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {f arg : Expr Nat} :
      AppVerdict D σ ρ (AppRead.no : AppRead Aw src E n Γ f arg)

/-- A verdict moves onto another typing with the same erasure. -/
def AppVerdict.move {Ei Ei' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} {D : TyP Ei n Γ e T} {D' : TyP Ei' n Γ e' T'}
    {σ : Level → Level} {ρ : List Disp}
    {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {f arg : Expr Nat}
    {r : AppRead Aw src E n Γ f arg}
    (heq : D'.eps σ ρ = D.eps σ ρ) : AppVerdict D σ ρ r → AppVerdict D' σ ρ r
  | .clause h => .clause (heq.trans h)
  | .star h => .star (heq.trans h)
  | .raw => .raw
  | .none => .none

/-! ## §2 an application clause, transported

The pushed got is the one `pushAppWk` / `pushAppLinst` / `pushAppEsub`
build. Its erasures are the inner got's, moved by the same transport. -/

theorem wk_app_skip {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {f₀ a₀ : Expr Nat}
    (g : AppGot Aw src E n Γ₀ f₀ a₀) {f arg : Expr Nat}
    (hf : lift c 1 f₀ = f) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (hD : D.eps σ (removeAt ρ c) = appClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      appClause ((tyCast hf rfl (TyP.wk E n Γ₀ f₀ (.pi g.A g.B) d c g.hf)).eps σ ρ)
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.A d c g.ha)).eps σ ρ) := by
  rw [eps_wk_not_keep hk, hD, eps_tyCast, eps_tyCast, eps_wk_not_keep hk,
    eps_wk_not_keep hk]
  rfl

theorem wk_app_keep {Em : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {d : LocalDecl} {c : Nat} (D : TyP Em n Γ₀ e T)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {f₀ a₀ : Expr Nat}
    (g : AppGot Aw src E n Γ₀ f₀ a₀) {f arg : Expr Nat}
    (hf : lift c 1 f₀ = f) (ha : lift c 1 a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep)
    (hD : D.eps σ (removeAt ρ c) = appClauseOf g σ (removeAt ρ c)) :
    (TyP.wk Em n Γ₀ e T d c D).eps σ ρ =
      appClause ((tyCast hf rfl (TyP.wk E n Γ₀ f₀ (.pi g.A g.B) d c g.hf)).eps σ ρ)
        ((tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.A d c g.ha)).eps σ ρ) := by
  rw [eps_wk_keep hk, hD, eps_tyCast, eps_tyCast, eps_wk_keep hk, eps_wk_keep hk]
  exact lift_appClause _ _ _ _

theorem linst_app_yes {Em : ResolvedEnv} {a n : Nat} {Γ₀ : LCtx}
    {e T₀ : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D : TyP Em a Γ₀ e T₀)
    {E : ResolvedEnv} {Aw : Nat → Nat} {src : Nat} {f₀ a₀ : Expr Nat}
    (g : AppGot Aw src E a Γ₀ f₀ a₀) {f arg : Expr Nat}
    (hf : instantiateLevels ls f₀ = f) (ha : instantiateLevels ls a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hD : D.eps (fun l => σ (instLevel ls l)) ρ =
      appClauseOf g (fun l => σ (instLevel ls l)) ρ) :
    (TyP.linst Em a n Γ₀ e T₀ ls hls hlen D).eps σ ρ =
      appClause
        ((tyCast hf rfl (TyP.linst E a n Γ₀ f₀ (.pi g.A g.B) ls hls hlen g.hf)).eps σ ρ)
        ((tyCast ha rfl (TyP.linst E a n Γ₀ a₀ g.A ls hls hlen g.ha)).eps σ ρ) := by
  rw [eps_linst, hD, eps_tyCast, eps_tyCast, eps_linst, eps_linst]
  rfl

theorem esub_app_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {f₀ a₀ : Expr Nat}
    (g : AppGot Aw src E n Γ₀ f₀ a₀) {f arg : Expr Nat}
    (hfEq : instantiate j (lift 0 j repl) f₀ = f)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    (hD : D.eps σ (insertDisp .drop j ρ) = appClauseOf g σ (insertDisp .drop j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      appClause
        ((tyCast hfEq rfl
            (TyP.esub E n Γ₀ f₀ (.pi g.A g.B) t repl j uE g.hf hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ)
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.A t repl j uE g.ha hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ) := by
  rw [eps_esub_drop (hu := hu), hD, eps_tyCast, eps_tyCast, eps_esub_drop (hu := hu),
    eps_esub_drop (hu := hu)]
  rfl

/-- A relevant hole: `inst_appClause`. The replacement must not erase to `★`. -/
theorem esub_app_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat} {j : Nat} {uE : Level}
    (D : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Aw : Nat → Nat} {src : Nat} {f₀ a₀ : Expr Nat}
    (g : AppGot Aw src E n Γ₀ f₀ a₀) {f arg : Expr Nat}
    (hfEq : instantiate j (lift 0 j repl) f₀ = f)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false) (hr : hv.eps σ ρ ≠ .star)
    (hD : D.eps σ (insertDisp .keep j ρ) = appClauseOf g σ (insertDisp .keep j ρ)) :
    (TyP.esub Ei n Γ₀ e T t repl j uE D hget hv hvT).eps σ ρ =
      appClause
        ((tyCast hfEq rfl
            (TyP.esub E n Γ₀ f₀ (.pi g.A g.B) t repl j uE g.hf hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ)
        ((tyCast haEq rfl
            (TyP.esub E n Γ₀ a₀ g.A t repl j uE g.ha hget
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)
                hext hv)
              (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)
                hext hvT))).eps σ ρ) := by
  rw [eps_esub_keep (hu := hu), hD, eps_tyCast, eps_tyCast, eps_esub_keep (hu := hu),
    eps_esub_keep (hu := hu), eps_ewk]
  exact inst_appClause _ hr _ _

/-! ## §3 the walk -/

def appVerdict_node {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx} {f arg A B : Expr Nat}
    {w : Level}
    (hf : TyP Ei n Γ f (.pi A B)) (ha : TyP Ei n Γ arg A)
    (hT : TyP Ei n Γ (instantiate0 arg B) (.sort w))
    (hAt : ∀ y ∈ (TyP.app Ei n Γ f arg A B w hf ha hT).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp) :
    AppVerdict (TyP.app Ei n Γ f arg A B w hf ha hT) σ ρ
      (readApp hext Aw src (TyP.app Ei n Γ f arg A B w hf ha hT) rfl hAt) := by
  unfold readApp
  refine .clause ?_
  rw [eps_app_appClause]
  rfl

def appVerdict_conv {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (inner : TyP Ei n Γ e A) (hc : CvP Ei n Γ A B (.sort u))
    {f arg : Expr Nat} (he : e = .app f arg)
    (hAt : ∀ y ∈ (TyP.conv Ei n Γ e A B u inner hc).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    (ih : AppVerdict inner σ ρ
      (readApp hext Aw src inner he (conv_atom_src Aw inner hc hAt))) :
    AppVerdict (TyP.conv Ei n Γ e A B u inner hc) σ ρ
      (readApp hext Aw src (TyP.conv Ei n Γ e A B u inner hc) he hAt) := by
  unfold readApp
  exact ih.move (eps_conv σ ρ)

def appVerdict_ewk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {E₀ : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (hext' : EnvExt E₀ Ei) (inner : TyP E₀ n Γ e A)
    {f arg : Expr Nat} (he : e = .app f arg)
    (hAt : ∀ y ∈ (TyP.ewk E₀ Ei n Γ e A hext' inner).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    (ih : AppVerdict inner σ ρ
      (readApp (envExt_trans hext' hext) Aw src inner he
        (ewk_atom_src Aw hext' inner hAt))) :
    AppVerdict (TyP.ewk E₀ Ei n Γ e A hext' inner) σ ρ
      (readApp hext Aw src (TyP.ewk E₀ Ei n Γ e A hext' inner) he hAt) := by
  unfold readApp
  exact ih.move (eps_ewk σ ρ)

def appVerdict_wk {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {d : LocalDecl} {c : Nat} (inner : TyP Ei n Γ₀ e₀ T₀)
    {f arg : Expr Nat} (he : lift c 1 e₀ = .app f arg)
    (hAt : ∀ y ∈ (TyP.wk Ei n Γ₀ e₀ T₀ d c inner).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    {f₀ a₀ : Expr Nat} {he₀ : e₀ = .app f₀ a₀}
    {hf₀ : lift c 1 f₀ = f} {ha₀ : lift c 1 a₀ = arg}
    (hF : lift_eq_app he = .mk f₀ a₀ he₀ hf₀ ha₀)
    (ih : AppVerdict inner σ (removeAt ρ c)
      (readApp hext Aw src inner he₀ (wk_atom_src Aw inner hAt))) :
    AppVerdict (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) σ ρ
      (readApp hext Aw src (TyP.wk Ei n Γ₀ e₀ T₀ d c inner) he hAt) := by
  unfold readApp
  rw [hF]
  dsimp
  cases hri : readApp hext Aw src inner he₀ (wk_atom_src Aw inner hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushAppWk]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushAppWk]
          exact .raw
      | star h =>
          simp only [pushAppWk]
          exact .star (eps_wk_star h)
      | clause h =>
          simp only [pushAppWk]
          refine .clause ?_
          simp only [appClauseOf]
          cases hρ : ρ[c]? with
          | none =>
              exact wk_app_skip inner g hf₀ ha₀ σ ρ (Or.inl hρ) h
          | some disp =>
              cases disp with
              | drop =>
                  exact wk_app_skip inner g hf₀ ha₀ σ ρ (Or.inr (Or.inl hρ)) h
              | inline v =>
                  exact wk_app_skip inner g hf₀ ha₀ σ ρ (Or.inr (Or.inr ⟨v, hρ⟩)) h
              | keep =>
                  exact wk_app_keep inner g hf₀ ha₀ σ ρ hρ h

def appVerdict_linst {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {a n : Nat} {Γ₀ : LCtx} {e₀ T₀ : Expr Nat}
    {ls : List Level} (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (inner : TyP Ei a Γ₀ e₀ T₀)
    {f arg : Expr Nat} (he : instantiateLevels ls e₀ = .app f arg)
    (hAt : ∀ y ∈ (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp)
    {f₀ a₀ : Expr Nat} {he₀ : e₀ = .app f₀ a₀}
    {hf₀ : instantiateLevels ls f₀ = f} {ha₀ : instantiateLevels ls a₀ = arg}
    (hF : instantiateLevels_eq_app he = .mk f₀ a₀ he₀ hf₀ ha₀)
    (ih : AppVerdict inner (fun l => σ (instLevel ls l)) ρ
      (readApp hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt))) :
    AppVerdict (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) σ ρ
      (readApp hext Aw src (TyP.linst Ei a n Γ₀ e₀ T₀ ls hls hlen inner) he hAt) := by
  unfold readApp
  rw [hF]
  dsimp
  cases hri : readApp hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushAppLinst]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushAppLinst]
          exact .raw
      | star h =>
          simp only [pushAppLinst]
          exact .star (eps_linst_star h)
      | clause h =>
          simp only [pushAppLinst]
          refine .clause ?_
          simp only [appClauseOf]
          exact linst_app_yes hls hlen inner g hf₀ ha₀ σ ρ h

def appVerdict_esub_drop {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {f arg : Expr Nat} (he : instantiate j (lift 0 j repl) e = .app f arg)
    (hAt : ∀ y ∈ (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT).atoms Aw,
      y < src)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = true)
    {f₀ a₀ : Expr Nat} {he₀ : e = .app f₀ a₀}
    {hf₀ : instantiate j (lift 0 j repl) f₀ = f}
    {ha₀ : instantiate j (lift 0 j repl) a₀ = arg}
    (hF : instantiate_eq_app he = .under f₀ a₀ he₀ hf₀ ha₀)
    (ih : AppVerdict inner σ (insertDisp .drop j ρ)
      (readApp hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt))) :
    AppVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readApp hext Aw src
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he hAt) := by
  unfold readApp
  rw [hF]
  dsimp
  cases hri : readApp hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushAppEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushAppEsub]
          exact .raw
      | star h =>
          simp only [pushAppEsub]
          exact .star (eps_esub_drop_star hu h)
      | clause h =>
          simp only [pushAppEsub]
          refine .clause ?_
          simp only [appClauseOf]
          exact esub_app_drop hext inner hget hv hvT g hf₀ ha₀ σ ρ hu h

def appVerdict_esub_keep {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {f arg : Expr Nat} (he : instantiate j (lift 0 j repl) e = .app f arg)
    (hAt : ∀ y ∈ (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT).atoms Aw,
      y < src)
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ uE) = false)
    {f₀ a₀ : Expr Nat} {he₀ : e = .app f₀ a₀}
    {hf₀ : instantiate j (lift 0 j repl) f₀ = f}
    {ha₀ : instantiate j (lift 0 j repl) a₀ = arg}
    (hF : instantiate_eq_app he = .under f₀ a₀ he₀ hf₀ ha₀)
    (ih : AppVerdict inner σ (insertDisp .keep j ρ)
      (readApp hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt))) :
    AppVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readApp hext Aw src
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he hAt) := by
  unfold readApp
  rw [hF]
  dsimp
  cases hri : readApp hext Aw src inner he₀ (esub_inner_src Aw inner hget hv hvT hAt) with
  | no =>
      rw [hri] at ih
      cases ih
      simp only [pushAppEsub]
      exact .none
  | yes g =>
      rw [hri] at ih
      cases ih with
      | raw =>
          simp only [pushAppEsub]
          exact .raw
      | star h =>
          simp only [pushAppEsub]
          exact .star (eps_esub_keep_star hu h)
      | clause h =>
          by_cases hr : hv.eps σ ρ = .star
          · simp only [pushAppEsub]
            exact .raw
          · simp only [pushAppEsub]
            refine .clause ?_
            simp only [appClauseOf]
            exact esub_app_keep hext inner hget hv hvT g hf₀ ha₀ σ ρ hu hr h

/-- The substituted variable is the application. The replacement's verdict
    is the outer verdict once the variable hits; a proof variable is `★`. -/
noncomputable def appVerdict_bare {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {f arg : Expr Nat} (he : instantiate j (lift 0 j repl) e = .app f arg)
    (hAt : ∀ y ∈ (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT).atoms Aw,
      y < src)
    (σ : Level → Level) (ρ : List Disp)
    (hs : e = .bvar j) (hr : lift 0 j repl = .app f arg)
    (hI : instantiate_eq_app he = .here hs hr)
    (ihV : AppVerdict hv σ ρ
      (readApp hext Aw src hv hr (esub_val_src Aw inner hget hv hvT hAt))) :
    AppVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readApp hext Aw src
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he hAt) := by
  unfold readApp
  rw [hI]
  dsimp
  cases hri : readApp hext Aw src hv hr (esub_val_src Aw inner hget hv hvT hAt) with
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
noncomputable def epsWalkApp {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    (src : Nat) (σ : Level → Level) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {f arg : Expr Nat} → (he : e = .app f arg) →
    (hAt : ∀ y ∈ D.atoms Aw, y < src) → (ρ : List Disp) →
    AppVerdict D σ ρ (readApp hext Aw src D he hAt)
  | _, _, _, _, .sort .., _, _, he, _, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _, _ => by cases he
  | _, _, _, _, .pi .., _, _, he, _, _ => by cases he
  | _, _, _, _, .lam .., _, _, he, _, _ => by cases he
  | _, _, _, _, .app _ _ _ f a A B w hf ha hT, _, _, he, hAt, ρ =>
      match f, a, he with
      | _, _, rfl => appVerdict_node hext Aw src hf ha hT hAt σ ρ
  | _, _, _, _, .letE .., _, _, he, _, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, he, hAt, ρ =>
      appVerdict_conv hext Aw src inner hc he hAt σ ρ
        (epsWalkApp hext Aw src σ inner he (conv_atom_src Aw inner hc hAt) ρ)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, hAt, ρ =>
      match hF : lift_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          appVerdict_wk hext Aw src inner he hAt σ ρ hF
            (epsWalkApp hext Aw src σ inner he₀ (wk_atom_src Aw inner hAt)
              (removeAt ρ c))
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, hAt, ρ =>
      match hF : instantiate_eq_app he with
      | .under f₀ a₀ he₀ hf₀ ha₀ =>
          match hu : levelIsZero (σ uE) with
          | true =>
              appVerdict_esub_drop hext Aw src inner hget hv hvT he hAt σ ρ hu hF
                (epsWalkApp hext Aw src σ inner he₀
                  (esub_inner_src Aw inner hget hv hvT hAt) (insertDisp .drop j ρ))
          | false =>
              appVerdict_esub_keep hext Aw src inner hget hv hvT he hAt σ ρ hu hF
                (epsWalkApp hext Aw src σ inner he₀
                  (esub_inner_src Aw inner hget hv hvT hAt) (insertDisp .keep j ρ))
      | .here hs hr =>
          appVerdict_bare hext Aw src inner hget hv hvT he hAt σ ρ hs hr hF
            (epsWalkApp hext Aw src σ hv hr (esub_val_src Aw inner hget hv hvT hAt) ρ)
  | _, _, _, _, .lsub .., _, _, _, _, _ => by
      unfold readApp
      exact .none
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, hAt, ρ =>
      match hF : instantiateLevels_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          appVerdict_linst hext Aw src hls hlen inner he hAt σ ρ hF
            (epsWalkApp hext Aw src (fun l => σ (instLevel ls l)) inner he₀
              (linst_atom_src Aw hls hlen inner hAt) ρ)
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he, hAt, ρ =>
      appVerdict_ewk hext Aw src hext' inner he hAt σ ρ
        (epsWalkApp (envExt_trans hext' hext) Aw src σ inner he
          (ewk_atom_src Aw hext' inner hAt) ρ)
  | _, _, _, _, .cctx .., _, _, _, _, _ => by
      unfold readApp
      exact .none

end Rcic.Syn

#print axioms Rcic.Syn.appClauseOf
#print axioms Rcic.Syn.AppVerdict.move
#print axioms Rcic.Syn.wk_app_skip
#print axioms Rcic.Syn.wk_app_keep
#print axioms Rcic.Syn.linst_app_yes
#print axioms Rcic.Syn.esub_app_drop
#print axioms Rcic.Syn.esub_app_keep
#print axioms Rcic.Syn.appVerdict_node
#print axioms Rcic.Syn.appVerdict_conv
#print axioms Rcic.Syn.appVerdict_ewk
#print axioms Rcic.Syn.appVerdict_wk
#print axioms Rcic.Syn.appVerdict_linst
#print axioms Rcic.Syn.appVerdict_esub_drop
#print axioms Rcic.Syn.appVerdict_esub_keep
#print axioms Rcic.Syn.appVerdict_bare
#print axioms Rcic.Syn.epsWalkApp
