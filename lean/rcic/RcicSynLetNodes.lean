import rcic.RcicSynLetGate

/-!
# Wall 2 (changed-declaration letRight), step 4 — the transported nodes' erasures and the
introduced-let display equation

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Introduced-let display equation".

`tyAtLet` rebuilds every rule node of the original in the final context (`tySort`, `tyConst`,
`tyPi`, `tyLam`, `tyApp`, `tyLet`, `tyLit`, with `toSort` / `toPi` / `moveUnderL` casts).
This module computes each rebuilt node's erasure in terms of its children's, in the same
clause shape as the original's (`gateOut`, `piSlot`, `lamErasure`, `appClause`, `letDisp`):

* the gate of a rebuilt node is `levelIsZero (μ' (Skels.appLevel ss u))`, which is the
  original node's gate under the stage map `fun l => μ' (Skels.appLevel ss l)`;
* `tyAtLet_letE_eps` is the introduced-let display equation: the rebuilt let's body is erased
  at `letDisp a' :: ρ'` where `a'` is the transported value's erasure — against the original's
  `letDisp a :: δ` with the pre-action value `a` (`let_eps_eq`); the two heads are related by
  `binderRel_letDisp` through the pending actions, so the source head holds the pre-action
  value and the actions are applied once, never twice. Native cutoff `j + 1`, erased cutoff
  unchanged (`binderActs` of a non-keep binder).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 casts and level lists -/

theorem eps_toSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e : Expr Nat} {ss : List Skel}
    {u : Level} (h : TyP E n Γ e (Skels.app ss (.sort u))) (σ : Level → Level) (ρ : List Disp) :
    (toSort h).eps σ ρ = h.eps σ ρ := eps_tyCast _ _ _ _ _

theorem eps_toPi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} {ss : List Skel}
    {A B : Expr Nat} (h : TyP E n Γ f (Skels.app ss (.pi A B))) (σ : Level → Level)
    (ρ : List Disp) : (toPi h).eps σ ρ = h.eps σ ρ := eps_tyCast _ _ _ _ _

theorem eps_moveUnderL {E : ResolvedEnv} {n k : Nat} {Dom' Val' : Expr Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {dLocal dFinal : LocalDecl} {body T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (h : TyP E n (setLetB (k + 1) Dom' Val' (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) body)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T))
    (σ : Level → Level) (ρ : List Disp) :
    (moveUnderL hd h).eps σ ρ = h.eps σ ρ := by
  unfold moveUnderL
  rw [eps_tyCastCtx, eps_tyCast]

/-- `Skels.appLevels` is the pointwise `Skels.appLevel`. -/
theorem appLevels_eq_map : (ss : List Skel) → (ls : List Level) →
    Skels.appLevels ss ls = ls.map (Skels.appLevel ss)
  | [], ls => by simp [Skels.appLevels, Skels.appLevel]
  | .wk c d :: ss, ls => by
      simp only [Skels.appLevels, Skels.appLevel]
      exact appLevels_eq_map ss ls
  | .esub j v :: ss, ls => by
      simp only [Skels.appLevels, Skels.appLevel]
      exact appLevels_eq_map ss ls
  | .linst ls₀ :: ss, ls => by
      simp only [Skels.appLevels, Skels.appLevel]
      rw [appLevels_eq_map ss, List.map_map]
      rfl
  | .cctx p A :: ss, ls => by
      simp only [Skels.appLevels, Skels.appLevel]
      exact appLevels_eq_map ss ls

/-! ## §2 the rebuilt nodes -/

theorem eps_tySort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (l k : Level) (h : eqN k (.succ l))
    (ss : List Skel) (σ : Level → Level) (ρ : List Disp) :
    (tySort (E := E) (n := n) (Γ := Γ) l k h ss).eps σ ρ = .sort (σ (Skels.appLevel ss l)) := by
  unfold tySort
  rw [eps_tyCast]
  rfl

theorem eps_tyConst {E : ResolvedEnv} (hE : CvWalkHyp E) {n nIn : Nat} {Γ : LCtx}
    {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true) (hls : eqNList ls ls₀)
    (ss : List (PStep E n)) (hfuel : FuelRel ss nIn)
    (hT : TyP E n Γ (Skels.app (steps ss) (instantiateLevels ls₀ m.mtype))
        (.sort (Skels.appLevel (steps ss) u)))
    (σ : Level → Level) (ρ : List Disp) :
    (tyConst hE hres hlen hwf hls ss hfuel hT).eps σ ρ =
      gateOut (levelIsZero (σ (Skels.appLevel (steps ss) u)))
        (.const r (ls.map (fun l => σ (Skels.appLevel (steps ss) l)))) := by
  unfold tyConst
  rw [eps_tyCast]
  cases hu : levelIsZero (σ (Skels.appLevel (steps ss) u))
  · rw [eps_const_rel hu, appLevels_eq_map, List.map_map]
    rfl
  · rw [eps_const_proof hu]
    rfl

/-- The original Π clause in one shape: domain, then the codomain under the binder's
    disposition with the R2 pad at a proof domain. -/
theorem eps_pi_bit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {B : Expr Nat} {v : Level} (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) (σ : Level → Level) (ρ : List Disp) :
    (TyP.pi E n Γ A u B v hA hB).eps σ ρ =
      .pi (hA.eps σ ρ)
        (piSlot (levelIsZero (σ u)) (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
  cases hu : levelIsZero (σ u)
  · rw [eps_pi_keep hu]; rfl
  · rw [eps_pi_drop hu]; rfl

theorem eps_tyPi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (A B : Expr Nat) (u v : Level)
    (ss : List Skel)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
        (Skels.app (ss.map Skel.shift) B)
        (.sort (Skels.appLevel (ss.map Skel.shift) v)))
    (σ : Level → Level) (ρ : List Disp) :
    (tyPi A B u v ss hA hB).eps σ ρ =
      .pi (hA.eps σ ρ)
        (piSlot (levelIsZero (σ (Skels.appLevel ss u)))
          (hB.eps σ (binderDisp (levelIsZero (σ (Skels.appLevel ss u))) :: ρ))) := by
  unfold tyPi
  rw [eps_tyCast]
  exact eps_pi_bit hA hB σ ρ

theorem eps_tyLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A body B : Expr Nat) (u v : Level) (ss : List Skel)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hbody : TyP E n (.assumption (Skels.app ss A) :: Γ)
        (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B))
    (hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
        (Skels.app (ss.map Skel.shift) B)
        (.sort (Skels.appLevel (ss.map Skel.shift) v)))
    (σ : Level → Level) (ρ : List Disp) :
    (tyLam A body B u v ss hA hbody hB).eps σ ρ =
      lamErasure (levelIsZero (σ (Skels.appLevel ss u)))
        (hbody.eps σ (binderDisp (levelIsZero (σ (Skels.appLevel ss u))) :: ρ)) := by
  unfold tyLam
  rw [eps_tyCast]
  exact eps_lam_clause hA hbody hB σ ρ

theorem eps_tyApp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (f a A B : Expr Nat) (w : Level) (ss : List Skel)
    (hf : TyP E n Γ (Skels.app ss f)
        (.pi (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)))
    (ha : TyP E n Γ (Skels.app ss a) (Skels.app ss A))
    (hT : TyP E n Γ (Skels.app ss (instantiate0 a B)) (.sort (Skels.appLevel ss w)))
    (σ : Level → Level) (ρ : List Disp) :
    (tyApp f a A B w ss hf ha hT).eps σ ρ = appClause (hf.eps σ ρ) (ha.eps σ ρ) := by
  unfold tyApp
  rw [eps_tyCast]
  exact eps_app_appClause hf ha _ σ ρ

theorem eps_tyLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A value B body : Expr Nat) (u w : Level) (ss : List Skel)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hv : TyP E n Γ (Skels.app ss value) (Skels.app ss A))
    (hb : TyP E n (.letBinding (Skels.app ss A) (Skels.app ss value) :: Γ)
        (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B))
    (hT : TyP E n Γ (Skels.app ss (instantiate0 value B)) (.sort (Skels.appLevel ss w)))
    (σ : Level → Level) (ρ : List Disp) :
    (tyLet A value B body u w ss hA hv hb hT).eps σ ρ = hb.eps σ (letDisp (hv.eps σ ρ) :: ρ) := by
  unfold tyLet
  rw [eps_tyCast]
  exact let_eps_eq hA hv hb _ σ ρ

theorem eps_tyLit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (ss : List Skel) (hexp : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T))
    (σ : Level → Level) (ρ : List Disp) :
    (tyLit t T ss hexp).eps σ ρ = hexp.eps σ ρ := by
  unfold tyLit
  rw [eps_tyCast, eps_lit, eps_tyCast]

/-! ## §3 the introduced-let display equation -/

/-- The rebuilt let's body is erased at `letDisp a' :: ρ'` with `a'` the transported value's
    erasure. -/
theorem tyAtLet_letE_eps {E Ei : ResolvedEnv} {n : Nat} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E)
    {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)}
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ)
    {A : Expr Nat} {u : Level} {value B body : Expr Nat} {w : Level}
    (hA : TyP Ei nIn Γ A (.sort u)) (hv : TyP Ei nIn Γ value A)
    (hb : TyP Ei nIn (.letBinding A value :: Γ) body B)
    (hT : TyP Ei nIn Γ (instantiate0 value B) (.sort w))
    (μ' : Level → Level) (ρ' : List Disp) :
    (tyAtLet hW ι ιenv hext p (TyP.letE Ei nIn Γ A u value B body w hA hv hb hT)).eps μ' ρ' =
      (tyAtLet hW ι ιenv hext
        (packLUnder p (.letBinding A value)
          (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
          (onDecl_let (steps ss) A value).symm) hb).eps μ'
        (letDisp ((tyAtLet hW ι ιenv hext p hv).eps μ' ρ') :: ρ') := by
  show (tyLet A value B body u w (steps ss) (toSort (tyAtLet hW ι ιenv hext p hA))
    (tyAtLet hW ι ιenv hext p hv)
    (moveUnderL (onDecl_let (steps ss) A value).symm
      (tyAtLet hW ι ιenv hext
        (packLUnder p (.letBinding A value)
          (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
          (onDecl_let (steps ss) A value).symm) hb))
    (toSort (tyAtLet hW ι ιenv hext p hT))).eps μ' ρ' = _
  rw [eps_tyLet, eps_moveUnderL]

end Rcic.Syn

#print axioms Rcic.Syn.eps_moveUnderL
#print axioms Rcic.Syn.appLevels_eq_map
#print axioms Rcic.Syn.eps_tySort
#print axioms Rcic.Syn.eps_tyConst
#print axioms Rcic.Syn.eps_pi_bit
#print axioms Rcic.Syn.eps_tyPi
#print axioms Rcic.Syn.eps_tyLam
#print axioms Rcic.Syn.eps_tyApp
#print axioms Rcic.Syn.eps_tyLet
#print axioms Rcic.Syn.eps_tyLit
#print axioms Rcic.Syn.tyAtLet_letE_eps
