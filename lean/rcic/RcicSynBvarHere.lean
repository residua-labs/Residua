import rcic.RcicSynBvarView
import rcic.RcicSynRead
import rcic.RcicSynBvarEpsWk
import rcic.RcicSynBvarEpsEsub
import rcic.RcicSynBvarEpsLsub

/-!
# Syntactic sortRow, build step 3ab — the bvar head follows the preserving transports

`research/rcic/semantic/S3_ES_ARMS.md` §26–§27. `epsReadLam` / `epsReadRedex`
return `raw` on `esub`-here: `cases` on a typing of `.bvar j` does not
eliminate `wk`. `bvarEps` is the head that does. It quantifies the term
first, the same split as `bvarHead`.

* the `bvar` node whose sort is a proof erases to `★` at every `ρ`;
* the `bvar` node whose sort is relevant erases to `resolve ρ j`;
* `conv`, `ewk`, `linst` and `cctx` preserve the term, so the head is
  the inner head (`linst` recomputes `σ`);
* `wk` follows the inner head across `removeAt` (`bvarEpsWk`). A `★` is
  preserved. A relevant variable below a non-`keep` stays, and one at or
  above a `drop`, an `inline` or a `keep` is the shifted index. A `keep`
  strictly above the index, and a missing entry at or above it, stay
  `other`;
* `esub` follows the inner head across `insertDisp` (`bvarEpsEsub`).
  A `★` is preserved. A relevant variable below an in-range `drop`
  stays, and one at or above an in-range `drop` or `keep` is the
  shifted index. The hole on `drop` is `★`; on `keep` it is the
  replacement. A `keep` strictly above the index, and a short list,
  stay `other`;
* `lsub` follows the inner head across `insertDisp` (`bvarEpsLsub`).
  A `★` value inserts `drop`; any other value inserts `inline` of
  that erasure. A `★` body is preserved. A relevant variable below an
  in-range hole stays, and one at or above an in-range `drop` or
  `inline` is the shifted index. The hole on `drop` is `★`. The hole
  on `inline` is the lifted value, so it stays `other`. A short list
  stays `other`;

`epsWalkLam` / `epsWalkRedex` are the walks with that head on the here
spine. The other arms are the §25 helpers. `epsReadLam` is unchanged.

On `drop`, a proof node is `★`, and a relevant node is `★` when
`j ≤ ρ.length` (`resolve_insertDisp_drop`). On `keep`, a proof node is
`★` because `inst` fixes `★`. A relevant node in range erases to
`bvar (countKeep (ρ.take j))`, so a `clause` or `star` verdict on the
replacement is the same verdict on the `esub` (`inst_bvar_hit`).
`raw` on the replacement stays `raw`: the hit is there, the
replacement's erasure is not. Out of range stays `raw`. A short context
misses the inserted disposition.

The descent is `Nat.strongRecOn` on the node's weight. `Nat.strongRecOn`
has no executable code, so the head and the walks that call it are
`noncomputable`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 what a typing of `.bvar j` erases to -/

/-- Erasure of a typing of `.bvar i`. `star` is the proof node. `rel` is
    the relevant node, at `resolve ρ i`. `other` is every remaining head. -/
inductive BvarEps {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {T : Expr Nat}
    (D : TyP E n Γ (.bvar i) T) (σ : Level → Level) (ρ : List Disp) : Type where
  | star (h : D.eps σ ρ = .star)
  | rel (h : D.eps σ ρ = resolve ρ i)
  | other

/-- An erasure equation moves a `star` or `rel` head onto another typing
    of the same variable. `other` stays `other`. -/
def bvarEpsCast {E E' : ResolvedEnv} {n n' : Nat} {Γ Γ' : LCtx} {i : Nat}
    {T T' : Expr Nat} {σ σ' : Level → Level} {ρ : List Disp}
    {D : TyP E n Γ (.bvar i) T} {D' : TyP E' n' Γ' (.bvar i) T'}
    (hD : D.eps σ ρ = D'.eps σ' ρ) : BvarEps D' σ' ρ → BvarEps D σ ρ
  | .star h => .star (hD.trans h)
  | .rel h => .rel (hD.trans h)
  | .other => .other

/-- `wk` of a variable, from the inner head at `removeAt ρ c`. The inner
    index is `i` below the cutoff and `i₀` at or above it. -/
def bvarEpsWk {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e₀ A : Expr Nat}
    {d : LocalDecl} {c i : Nat} (inner : TyP E n Γ₀ e₀ A)
    (he : lift c 1 e₀ = .bvar i) (σ : Level → Level) (ρ : List Disp)
    (child : ∀ {i₀ : Nat}, (hs : e₀ = .bvar i₀) →
      BvarEps (tyCast hs rfl inner) σ (removeAt ρ c)) :
    BvarEps (tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner)) σ ρ := by
  cases lift_eq_bvar he with
  | below hlo hs =>
    have got := child hs
    cases got with
    | other => exact .other
    | star h =>
      exact .star ((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
        (eps_wk_star ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h)))
    | rel h =>
      cases hρ : ρ[c]? with
      | none =>
        exact .rel ((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
          (eps_wk_rel_lo hlo (Or.inl hρ)
            ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h)))
      | some disp =>
        cases disp with
        | drop =>
          exact .rel ((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
            (eps_wk_rel_lo hlo (Or.inr (Or.inl hρ))
              ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h)))
        | inline v =>
          exact .rel ((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
            (eps_wk_rel_lo hlo (Or.inr (Or.inr ⟨v, hρ⟩))
              ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h)))
        | keep => exact .other
  | shift i₀ hge hs hi =>
    have got := child hs
    cases got with
    | other => exact .other
    | star h =>
      exact .star ((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
        (eps_wk_star ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h)))
    | rel h =>
      cases hρ : ρ[c]? with
      | none => exact .other
      | some disp =>
        cases disp with
        | drop =>
          exact .rel (((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
            (eps_wk_rel_hi_drop hge hρ
              ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h))).trans
            (congrArg (resolve ρ) hi.symm))
        | inline v =>
          exact .rel (((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
            (eps_wk_rel_hi_inline hge hρ
              ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h))).trans
            (congrArg (resolve ρ) hi.symm))
        | keep =>
          exact .rel (((eps_tyCast he rfl (TyP.wk E n Γ₀ e₀ A d c inner) σ ρ).trans
            (eps_wk_rel_hi_keep hge hρ
              ((eps_tyCast hs rfl inner σ (removeAt ρ c)).symm.trans h))).trans
            (congrArg (resolve ρ) hi.symm))

/-- `esub` of a variable. Below an in-range `drop` the index stays. At or
    above an in-range `drop` or `keep` it is the shifted index. The hole
    on `drop` is `★`; on `keep` it is the replacement's head. A `keep`
    strictly above the index, and a short list, stay `other`. -/
def bvarEpsEsub {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e₀ A t v : Expr Nat}
    {j i : Nat} {u : Level} (inner : TyP E n Γ₀ e₀ A)
    (hv : TyP E n (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ₀) (lift 0 j t) (.sort u))
    (hget : Γ₀[j]? = some (.assumption t))
    (he : instantiate j (lift 0 j v) e₀ = .bvar i)
    (σ : Level → Level) (ρ : List Disp)
    (child : ∀ {i₀ : Nat} (hs : e₀ = .bvar i₀) (ρ' : List Disp),
      BvarEps (tyCast hs rfl inner) σ ρ')
    (repl : (hs : lift 0 j v = .bvar i) → BvarEps (tyCast hs rfl hv) σ ρ) :
    BvarEps (tyCast he rfl
      (TyP.esub E n Γ₀ e₀ A t v j u inner hget hv hvT)) σ ρ := by
  let node := TyP.esub E n Γ₀ e₀ A t v j u inner hget hv hvT
  have castN : (tyCast he rfl node).eps σ ρ = node.eps σ ρ :=
    eps_tyCast he rfl node σ ρ
  cases instantiate_eq_bvar he with
  | below hlo hs =>
    cases hu : levelIsZero (σ u) with
    | true =>
      have got := child hs (insertDisp .drop j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_esub_star_drop hu
          ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_esub_rel_drop_lo hu hlo hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
        · exact .other
    | false =>
      have got := child hs (insertDisp .keep j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_esub_star_keep hu
          ((eps_tyCast hs rfl inner σ (insertDisp .keep j ρ)).symm.trans h)))
      | rel _ => exact .other
  | above i₀ hgt hs hi =>
    cases hi
    have hj : j ≤ i := Nat.le_of_lt_succ hgt
    cases hu : levelIsZero (σ u) with
    | true =>
      have got := child hs (insertDisp .drop j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_esub_star_drop hu
          ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_esub_rel_drop_hi hu hj hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
        · exact .other
    | false =>
      have got := child hs (insertDisp .keep j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_esub_star_keep hu
          ((eps_tyCast hs rfl inner σ (insertDisp .keep j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_esub_rel_keep_hi hu hj hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .keep j ρ)).symm.trans h)))
        · exact .other
  | here hs hr =>
    cases hu : levelIsZero (σ u) with
    | true =>
      have got := child hs (insertDisp .drop j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_esub_star_drop hu
          ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .star (castN.trans (eps_esub_hole_drop hu hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
        · exact .other
    | false =>
      have got := child hs (insertDisp .keep j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_esub_star_keep hu
          ((eps_tyCast hs rfl inner σ (insertDisp .keep j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · have hOuter : (tyCast he rfl node).eps σ ρ = hv.eps σ ρ :=
            castN.trans (eps_esub_hole_keep hu hlen
              ((eps_tyCast hs rfl inner σ (insertDisp .keep j ρ)).symm.trans h))
          cases repl hr with
          | other => exact .other
          | star hR =>
            exact .star (hOuter.trans
              ((eps_tyCast hr rfl hv σ ρ).symm.trans hR))
          | rel hR =>
            exact .rel (hOuter.trans
              ((eps_tyCast hr rfl hv σ ρ).symm.trans hR))
        · exact .other

/-- `lsub` of a variable. A `★` value inserts `drop`; any other value
    inserts `inline` of that erasure. Below an in-range hole the index
    stays. At or above an in-range `drop` or `inline` it is the shifted
    index. The hole on `drop` is `★`. The hole on `inline` is the value
    lifted by the newer `keep`s, so it stays `other`. A short list stays
    `other`. -/
def bvarEpsLsub {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e₀ A t v : Expr Nat}
    {j i : Nat} {u : Level} (inner : TyP E n Γ₀ e₀ A)
    (hv : TyP E n (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ₀) (lift 0 j t) (.sort u))
    (hget : Γ₀[j]? = some (.letBinding t v))
    (he : instantiate j (lift 0 j v) e₀ = .bvar i)
    (σ : Level → Level) (ρ : List Disp)
    (child : ∀ {i₀ : Nat} (hs : e₀ = .bvar i₀) (ρ' : List Disp),
      BvarEps (tyCast hs rfl inner) σ ρ') :
    BvarEps (tyCast he rfl
      (TyP.lsub E n Γ₀ e₀ A t v j u inner hget hv hvT)) σ ρ := by
  let node := TyP.lsub E n Γ₀ e₀ A t v j u inner hget hv hvT
  have castN : (tyCast he rfl node).eps σ ρ = node.eps σ ρ :=
    eps_tyCast he rfl node σ ρ
  cases instantiate_eq_bvar he with
  | below hlo hs =>
    by_cases hstar : hv.eps σ ρ = .star
    · have got := child hs (insertDisp .drop j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_lsub_star_drop hstar
          ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_lsub_rel_drop_lo hstar hlo hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
        · exact .other
    · have got := child hs (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_lsub_star_inline hstar
          ((eps_tyCast hs rfl inner σ
            (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_lsub_rel_inline_lo hstar hlo hlen
            ((eps_tyCast hs rfl inner σ
              (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)).symm.trans h)))
        · exact .other
  | above i₀ hgt hs hi =>
    cases hi
    have hj : j ≤ i := Nat.le_of_lt_succ hgt
    by_cases hstar : hv.eps σ ρ = .star
    · have got := child hs (insertDisp .drop j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_lsub_star_drop hstar
          ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_lsub_rel_drop_hi hstar hj hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
        · exact .other
    · have got := child hs (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_lsub_star_inline hstar
          ((eps_tyCast hs rfl inner σ
            (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .rel (castN.trans (eps_lsub_rel_inline_hi hstar hj hlen
            ((eps_tyCast hs rfl inner σ
              (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)).symm.trans h)))
        · exact .other
  | here hs _ =>
    by_cases hstar : hv.eps σ ρ = .star
    · have got := child hs (insertDisp .drop j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_lsub_star_drop hstar
          ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
      | rel h =>
        by_cases hlen : j ≤ ρ.length
        · exact .star (castN.trans (eps_lsub_hole_drop hstar hlen
            ((eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)).symm.trans h)))
        · exact .other
    · have got := child hs (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)
      cases got with
      | other => exact .other
      | star h =>
        exact .star (castN.trans (eps_lsub_star_inline hstar
          ((eps_tyCast hs rfl inner σ
            (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ)).symm.trans h)))
      | rel _ => exact .other

/-- The head of an arbitrary typing whose term is `.bvar i`. `conv`,
    `ewk`, `linst` and `cctx` are the inner head. `linst` instantiates
    the level map. `wk` is `bvarEpsWk`. `esub` is `bvarEpsEsub`.
    `lsub` is `bvarEpsLsub`. The descent is the node's weight:
    each of those constructors pays `1 +` the inner typing. -/
noncomputable def bvarEpsAux {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (i : Nat) (he : e = .bvar i)
    (σ : Level → Level) (ρ : List Disp) :     BvarEps (tyCast he rfl D) σ ρ :=
  (Nat.strongRecOn (motive := fun w =>
      ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
        (D : TyP E n Γ e T), D.wt (fun _ => 0) = w →
        ∀ {i : Nat} (he : e = .bvar i) (σ : Level → Level) (ρ : List Disp),
          BvarEps (tyCast he rfl D) σ ρ)
    (D.wt (fun _ => 0))
    (fun w ih {E} {n} {Γ} {e} {T} D hw {i} he σ ρ => by
      cases D
      case bvar i' u hlook hA =>
        cases he
        cases hu : levelIsZero (σ u) with
        | true => exact .star (eps_bvar_proof hu)
        | false => exact .rel (eps_bvar_rel hu)
      case conv A u inner hc =>
        exact bvarEpsCast (by simp only [eps_tyCast, TyP.eps])
          (ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
            inner rfl he σ ρ)
      case ewk E₀ hext inner =>
        exact bvarEpsCast (by simp only [eps_tyCast, TyP.eps])
          (ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
            inner rfl he σ ρ)
      case cctx Γtail A A' u hA inner =>
        exact bvarEpsCast (by simp only [eps_tyCast, TyP.eps])
          (ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
            inner rfl he σ ρ)
      case linst a Γ₀ e₀ A ls hlen inner hls =>
        exact bvarEpsCast (by simp only [eps_tyCast, TyP.eps])
          (ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
            inner rfl (instantiateLevels_eq_bvar he)
            (fun l => σ (instLevel ls l)) ρ)
      case sort => exact .other
      case const => exact .other
      case pi => exact .other
      case lam => exact .other
      case app => exact .other
      case letE => exact .other
      case lit => exact .other
      case wk Γ₀ e₀ A d c inner =>
        exact bvarEpsWk (d := d) inner he σ ρ fun {i₀} hs =>
          ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
            inner rfl hs σ (removeAt ρ c)
      case esub Γ₀ e₀ A t v j u hget inner hv hvT =>
        exact bvarEpsEsub inner hv hvT hget he σ ρ
          (fun {i₀} hs ρ' =>
            ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
              inner rfl hs σ ρ')
          (fun hs =>
            ih (hv.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
              hv rfl hs σ ρ)
      case lsub Γ₀ e₀ A t v j u hget inner hv hvT =>
        exact bvarEpsLsub inner hv hvT hget he σ ρ
          (fun {i₀} hs ρ' =>
            ih (inner.wt (fun _ => 0)) (by rw [← hw]; simp only [TyP.wt]; omega)
              inner rfl hs σ ρ')))
    D rfl he σ ρ

/-- The `bvar` node, classified by its sort bit, after the transports
    that leave the variable in place. -/
noncomputable def bvarEps {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {T : Expr Nat}
    (D : TyP E n Γ (.bvar i) T) (σ : Level → Level) (ρ : List Disp) :
    BvarEps D σ ρ :=
  bvarEpsAux D i rfl σ ρ

/-- `inst` deletes nothing from `★`. A proof variable on the `keep` path
    is therefore `★` after the substitution. -/
theorem inst_star (j : Nat) (r : ETm) : ETm.inst j r .star = .star := rfl

/-! ## §2 the here spine, from that head -/

/-- What the here-variable contributes to the outer `esub`. `hit` is the
    index `inst` substitutes. -/
inductive BareHere {Ei : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {j : Nat} {uE : Level}
    (inner : TyP Ei n Γ₀ e T) (σ : Level → Level) (ρ : List Disp) : Type where
  | starDrop (hu : levelIsZero (σ uE) = true)
      (h : inner.eps σ (insertDisp .drop j ρ) = .star)
  | starKeep (hu : levelIsZero (σ uE) = false)
      (h : inner.eps σ (insertDisp .keep j ρ) = .star)
  | hit (hu : levelIsZero (σ uE) = false)
      (h : inner.eps σ (insertDisp .keep j ρ) = .bvar (countKeep (ρ.take j)))
  | raw

noncomputable def bareHere {Ei : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T) (hs : e = .bvar j)
    (σ : Level → Level) (ρ : List Disp) :
    BareHere (j := j) (uE := uE) inner σ ρ := by
  cases huE : levelIsZero (σ uE) with
  | true =>
    cases bvarEps (tyCast hs rfl inner) σ (insertDisp .drop j ρ) with
    | star h =>
      exact .starDrop huE (by
        rw [← eps_tyCast hs rfl inner σ (insertDisp .drop j ρ)]
        exact h)
    | rel h =>
      by_cases hj : j ≤ ρ.length
      · exact .starDrop huE (by
          rw [← eps_tyCast hs rfl inner σ (insertDisp .drop j ρ), h,
            resolve_insertDisp_drop j ρ hj])
      · exact .raw
    | other =>
      exact .raw
  | false =>
    cases bvarEps (tyCast hs rfl inner) σ (insertDisp .keep j ρ) with
    | star h =>
      exact .starKeep huE (by
        rw [← eps_tyCast hs rfl inner σ (insertDisp .keep j ρ)]
        exact h)
    | rel h =>
      by_cases hj : j ≤ ρ.length
      · exact .hit huE (by
          rw [← eps_tyCast hs rfl inner σ (insertDisp .keep j ρ), h,
            resolve_insertDisp_keep j ρ hj])
      · exact .raw
    | other =>
      exact .raw

/-! ## §3 the λ walk -/

noncomputable def lamVerdict_bare {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body : Expr Nat} (he : instantiate j (lift 0 j repl) e = .lam Al body)
    (σ : Level → Level) (ρ : List Disp)
    (hs : e = .bvar j) (hr : lift 0 j repl = .lam Al body)
    (hI : instantiate_eq_lam he = .here hs hr)
    (ihV : LamVerdict hv σ ρ (readLam hext Aw hv hr)) :
    LamVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readLam hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readLam
  rw [hI]
  dsimp
  cases hri : readLam hext Aw hv hr with
  | no =>
    rw [hri] at ihV
    cases ihV
    simp only [LamRead.raise]
    exact .none
  | yes g =>
    rw [hri] at ihV
    simp only [LamRead.raise]
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
        unfold lamClauseOf
        rfl

set_option maxHeartbeats 800000 in
noncomputable def epsWalkLam {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
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
        (epsWalkLam hext Aw σ inner he ρ)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, ρ =>
      match hL : lift_eq_lam he with
      | .mk A₀ b₀ he₀ hAe hb₀ =>
          lamVerdict_wk hext Aw inner he σ ρ hL
            (epsWalkLam hext Aw σ inner he₀ (removeAt ρ c))
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, ρ =>
      match hI : instantiate_eq_lam he with
      | .under A₀ b₀ he₀ hAe hBe =>
          match hu : levelIsZero (σ uE) with
          | true =>
              lamVerdict_esub_drop hext Aw inner hget hv hvT he σ ρ hu hI
                (epsWalkLam hext Aw σ inner he₀ (insertDisp .drop j ρ))
          | false =>
              lamVerdict_esub_keep hext Aw inner hget hv hvT he σ ρ hu hI
                (epsWalkLam hext Aw σ inner he₀ (insertDisp .keep j ρ))
      | .here hs hr =>
          lamVerdict_bare hext Aw inner hget hv hvT he σ ρ hs hr hI
            (epsWalkLam hext Aw σ hv hr ρ)
  | _, _, _, _, .lsub .., _, _, _, _ => by
      unfold readLam
      exact .none
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, ρ =>
      match hL : instantiateLevels_eq_lam he with
      | .mk A₀ b₀ he₀ hAe hb₀ =>
          lamVerdict_linst hext Aw hls hlen inner he σ ρ hL
            (epsWalkLam hext Aw (fun l => σ (instLevel ls l)) inner he₀ ρ)
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he, ρ =>
      lamVerdict_ewk hext Aw hext' inner he σ ρ
        (epsWalkLam (envExt_trans hext' hext) Aw σ inner he ρ)
  | _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA, _, _, he, ρ =>
      lamVerdict_cctx hext Aw D hA he σ ρ

/-! ## §4 the redex walk -/

noncomputable def redexVerdict_bare {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ₀ : LCtx} {e T t repl : Expr Nat}
    {j : Nat} {uE : Level} (inner : TyP Ei n Γ₀ e T)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {Al body arg : Expr Nat}
    (he : instantiate j (lift 0 j repl) e = .app (.lam Al body) arg)
    (σ : Level → Level) (ρ : List Disp)
    (hs : e = .bvar j) (hr : lift 0 j repl = .app (.lam Al body) arg)
    (hI : instantiate_eq_app he = .here hs hr)
    (ihV : RedexVerdict hv σ ρ (readRedex hext Aw hv hr)) :
    RedexVerdict (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) σ ρ
      (readRedex hext Aw
        (TyP.esub Ei n Γ₀ e T t repl j uE inner hget hv hvT) he) := by
  unfold readRedex
  rw [hI]
  dsimp
  cases hri : readRedex hext Aw hv hr with
  | no =>
    rw [hri] at ihV
    cases ihV
    simp only [RedexRead.raise]
    exact .none
  | yes g =>
    rw [hri] at ihV
    simp only [RedexRead.raise]
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
        unfold redexClauseOf
        rfl

set_option maxHeartbeats 800000 in
noncomputable def epsWalkRedex {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
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
            (epsWalkLam hext Aw σ hf rfl ρ)
  | _, _, _, _, .letE .., _, _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, _, he, ρ =>
      redexVerdict_conv hext Aw inner hc he σ ρ
        (epsWalkRedex hext Aw σ inner he ρ)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, _, he, ρ =>
      match hF : lift_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          match hL : lift_eq_lam hf₀ with
          | .mk A₀ b₀ heLam hAe hb₀ =>
              redexVerdict_wk hext Aw inner he σ ρ hF hL
                (epsWalkRedex hext Aw σ inner (app_of_lam he₀ heLam)
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
                    (epsWalkRedex hext Aw σ inner (app_of_lam he₀ heLam)
                      (insertDisp .drop j ρ))
              | false =>
                  redexVerdict_esub_keep hext Aw inner hget hv hvT he σ ρ hu
                    hF hL
                    (epsWalkRedex hext Aw σ inner (app_of_lam he₀ heLam)
                      (insertDisp .keep j ρ))
          | .here hs hr =>
              redexVerdict_born hext Aw inner hget hv hvT he σ ρ hF hs hr hL
      | .here hs hr =>
          redexVerdict_bare hext Aw inner hget hv hvT he σ ρ hs hr hF
            (epsWalkRedex hext Aw σ hv hr ρ)
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, _, he, ρ =>
      match hF : instantiateLevels_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          match hL : instantiateLevels_eq_lam hf₀ with
          | .mk A₀ b₀ heLam hAe hb₀ =>
              redexVerdict_linst hext Aw hls hlen inner he σ ρ hF hL
                (epsWalkRedex hext Aw (fun l => σ (instLevel ls l)) inner
                  (app_of_lam he₀ heLam) ρ)
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, _, he, ρ =>
      redexVerdict_ewk hext Aw hext' inner he σ ρ
        (epsWalkRedex (envExt_trans hext' hext) Aw σ inner he ρ)
  | _, _, _, _, .lsub .., _, _, _, _, _ => by
      unfold readRedex
      exact .none
  | _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA, _, _, _, he, ρ =>
      redexVerdict_cctx hext Aw D hA he σ ρ

end Rcic.Syn

#print axioms Rcic.Syn.bvarEpsWk
#print axioms Rcic.Syn.bvarEpsEsub
#print axioms Rcic.Syn.bvarEpsLsub
#print axioms Rcic.Syn.bvarEpsCast
#print axioms Rcic.Syn.bvarEpsAux
#print axioms Rcic.Syn.bvarEps
#print axioms Rcic.Syn.inst_star
#print axioms Rcic.Syn.bareHere
#print axioms Rcic.Syn.lamVerdict_bare
#print axioms Rcic.Syn.epsWalkLam
#print axioms Rcic.Syn.redexVerdict_bare
#print axioms Rcic.Syn.epsWalkRedex
