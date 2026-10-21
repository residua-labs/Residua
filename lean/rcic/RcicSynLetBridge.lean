import rcic.RcicSynLetNodes

/-!
# Wall 2 (changed-declaration letRight), step 5 — the LetBridge induction

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Induction".

For an original typing `D` at a stage of the let-slot walk (stack `ss`, pack `p`, left
display `δ`, pending erased actions `acts`, site data `s`, right display `ρ'`), with the
stage map `stageMap μ' (steps ss) = fun l => μ' (Skels.appLevel (steps ss) l)`:

    Rel tbl (applyActs acts (D.eps (stageMap μ' (steps ss)) δ))
            ((tyAtLet hW ι ιenv hext p D).eps μ' ρ')

by induction on the original tree `D`. Stripping a transport lengthens the stack but
selects a smaller original typing; the replacement recursion at `esub`/`lsub` selects the
original child `hv`. The hypotheses are exactly: the trace invariant of the stage
(`TraceInv`), the structural facts (`AssumpPref`, weak `DisplayFits`, non-★ actions), and the
per-node answers `BodyAnswers`, which holds at every node of `D` precisely the answers Part
III names for it — the bvar gates (`BvarGate`: slot provider / replacement `W` through the
site gate / chain junctions + end), the per-stage replacement `PBit` at `esub`/`lsub`, and at
`lsub` the same-stage scope certificate (Part II's structural theorem, consumed as a
hypothesis here, never an ES/CL/observation answer). No field is equivalent to the goal.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the stage map -/

/-- The level map of a stage: the final map after the stack's level instantiations. -/
def stageMap (μ' : Level → Level) (ss : List Skel) : Level → Level :=
  fun l => μ' (Skels.appLevel ss l)

theorem stageMap_shift (μ' : Level → Level) {E : ResolvedEnv} {n : Nat} (dL dF : LocalDecl)
    (ss : List (PStep E n)) :
    stageMap μ' (steps (shiftAll dL dF ss)) = stageMap μ' (steps ss) := by
  funext l
  simp only [stageMap]
  rw [steps_shiftAll, appLevel_shift]

/-! ## §2 glue -/

theorem eps_const_gateOut {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u : Level} {hres : E.members r = some m} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true} {hls : eqNList ls ls₀}
    {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT).eps σ ρ =
      gateOut (levelIsZero (σ u)) (.const r (ls.map σ)) := by
  cases hu : levelIsZero (σ u)
  · exact eps_const_rel hu
  · exact eps_const_proof hu

theorem binderActs_binderDisp (b : Bool) (acts : List EAct) :
    binderActs (binderDisp b) acts = if b then acts else shiftActs acts := by
  cases b <;> rfl

theorem binderActs_letDisp (a : ETm) (acts : List EAct) : binderActs (letDisp a) acts = acts := by
  cases a <;> rfl

theorem applyActs_shift_piSlot (acts : List EAct) (b : Bool) (q : ETm) :
    applyActs (shiftActs acts) (piSlot b q) = piSlot b (applyActs (binderActs (binderDisp b) acts) q) := by
  cases b
  · rfl
  · exact applyActs_shift_lift acts q

theorem binderRel_binderDisp (tbl : List CRule) (acts : List EAct) (b : Bool) :
    BinderRel tbl acts (binderDisp b) (binderDisp b) := by
  cases b
  · exact .keep
  · exact .drop

theorem displayFits_binderDisp {Γ : LCtx} {δ : List Disp} (A : Expr Nat) (b : Bool)
    (h : DisplayFits Γ δ) : DisplayFits (.assumption A :: Γ) (binderDisp b :: δ) := by
  cases b
  · exact .assumptionKeep h
  · exact .assumptionDrop h

theorem displayFits_letDisp {Γ : LCtx} {δ : List Disp} (A v : Expr Nat) (a : ETm)
    (h : DisplayFits Γ δ) : DisplayFits (.letBinding A v :: Γ) (letDisp a :: δ) := by
  cases a
  all_goals first
    | exact DisplayFits.letDrop h
    | exact DisplayFits.letInline h

theorem displayFits_of_instLvlsCtx (ls : List Level) : (Γ : LCtx) → {δ : List Disp} →
    DisplayFits (instLvlsCtx ls Γ) δ → DisplayFits Γ δ
  | [], δ, _ => .nil δ
  | .assumption A :: Γ, δ, h => by
      rw [instLvlsCtx_cons] at h
      cases h with
      | assumptionKeep h' => exact .assumptionKeep (displayFits_of_instLvlsCtx ls Γ h')
      | assumptionDrop h' => exact .assumptionDrop (displayFits_of_instLvlsCtx ls Γ h')
  | .letBinding A v :: Γ, δ, h => by
      rw [instLvlsCtx_cons] at h
      cases h with
      | letDrop h' => exact .letDrop (displayFits_of_instLvlsCtx ls Γ h')
      | letInline h' => exact .letInline (displayFits_of_instLvlsCtx ls Γ h')

/-- The pending actions after an `esub`: a retained hole adds `inst κ r`. -/
def esubActs (b : Bool) (κ : Nat) (r : ETm) (acts : List EAct) : List EAct :=
  match b with
  | true => acts
  | false => .inst κ r :: acts

theorem eActsNonStar_esubActs {b : Bool} {κ : Nat} {r : ETm} {acts : List EAct}
    (hns : EActsNonStar acts) (hr : b = false → r ≠ .star) :
    EActsNonStar (esubActs b κ r acts) := by
  cases b
  · exact ⟨hr rfl, hns⟩
  · exact hns

theorem applyActs_eps_esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u : Level} (D : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (σ : Level → Level) (δ : List Disp) (acts : List EAct) :
    applyActs acts ((TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ δ) =
      applyActs (esubActs (levelIsZero (σ u)) (countKeep (δ.take j)) (hv.eps σ δ) acts)
        (D.eps σ (insertDisp (binderDisp (levelIsZero (σ u))) j δ)) := by
  cases hu : levelIsZero (σ u)
  · rw [eps_esub_keep hu]; rfl
  · rw [eps_esub_drop hu]; rfl

theorem applyActs_eps_wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl}
    {c : Nat} (D : TyP E n Γ e A) (σ : Level → Level) (δ : List Disp) (acts : List EAct) :
    applyActs acts ((TyP.wk E n Γ e A d c D).eps σ δ) =
      applyActs (wkActs δ c acts) (D.eps σ (removeAt δ c)) := by
  cases hk : δ[c]? with
  | none => rw [eps_wk_not_keep (Or.inl hk), wkActs_drop_none hk]
  | some dc =>
      cases dc with
      | keep => rw [eps_wk_keep hk, wkActs_keep hk]; rfl
      | drop => rw [eps_wk_not_keep (Or.inr (Or.inl hk)), wkActs_drop hk]
      | inline w => rw [eps_wk_not_keep (Or.inr (Or.inr ⟨w, hk⟩)), wkActs_inline hk]
where
  wkActs_drop_none {δ : List Disp} {c : Nat} (h : δ[c]? = none) (acts : List EAct) :
      wkActs δ c acts = acts := by
    simp only [wkActs, h]

/-- The `lsub` trace step in display form: `lsubDisp κ r` is `drop` at ★ and the localized
    inline otherwise. -/
theorem traceInv_lsub {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ0 : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx} (hget : Γe.get? j = some (.letBinding t v))
    {repl replT : Expr Nat} (hvS : TyP E n Γr repl replT)
    (hΓ : Γ0 = Γe) (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
    (hr : repl = Skels.app (steps ss) (lift 0 j v)) (hT : replT = Skels.app (steps ss) (lift 0 j t))
    {hrun : RunL k Dom' Val' ss (substRemove v j Γ0)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (substRemove v j Γ0) δ acts hinv hrun s)
    (hfit : DisplayFits (substRemove v j Γ0) δ)
    (hns : EActsNonStar acts)
    (σo : Level → Level) (uo : Level) (r : ETm)
    (hpb : r = .star ↔ levelIsZero (σo uo) = true)
    (hscope : r ≠ .star → AvoidPrefix (countKeep (δ.take j)) 0 r)
    (hrel : Rel tbl (applyActs acts r) (hvS.eps μ' ρ')) :
    TraceInv tbl μ' ρ' k Dom' Val' (.lsub j v t Γe Γr hget repl replT hvS :: ss) Γ0
      (insertDisp (lsubDisp (countKeep (δ.take j)) r) j δ) acts
      (.lsub j v t Γe Γr hget repl replT hvS hinv hr hT) (.lsub hΓ hctx hrun)
      (.lsub j v t Γe Γr hget repl replT hvS σo uo s) := by
  by_cases hrs : r = .star
  · subst hrs
    exact traceInv_lsub_drop hget hvS hΓ hctx hr hT h hfit σo uo .star hpb rfl hrel
  · have hd : lsubDisp (countKeep (δ.take j)) r = .inline (localize (countKeep (δ.take j)) r) := by
      cases r <;> first | rfl | exact absurd rfl hrs
    rw [hd]
    exact traceInv_lsub_inline hget hvS hΓ hctx hr hT h hfit hns σo uo r hpb hrs (hscope hrs) hrel

theorem lsubDisp_shape (κ : Nat) (r : ETm) :
    lsubDisp κ r = .drop ∨ ∃ w, lsubDisp κ r = .inline w := by
  cases r
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl⟩

theorem binderDisp_shape (b : Bool) : binderDisp b = .keep ∨ binderDisp b = .drop := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## §3 the per-node answers -/

/-- The answers consumed at the nodes of the original tree, each at its exact stage:
    bvar gates (`BvarGate`), per-stage replacement `PBit` at `esub` / `lsub`, and at `lsub`
    the same-stage scope certificate. Children are visited at exactly the stages `tyAtLet`
    visits them. -/
def BodyAnswers {E : ResolvedEnv} {n : Nat} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (tbl : List CRule) (μ' : Level → Level) :
    {Ei : ResolvedEnv} → (hext : EnvExt Ei E) →
    {nIn : Nat} → {Γ : LCtx} → {k : Nat} → {Dom Val Dom' Val' : Expr Nat} → {uSlot : Level} →
    {ss : List (PStep E n)} → {e T : Expr Nat} →
    (D : TyP Ei nIn Γ e T) → (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ) →
    (δ : List Disp) → (acts : List EAct) → (s : Sites ss) → (ρ' : List Disp) → Prop
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .sort .., _, _, _, _, _ => True
  | _, _, _, _, k, _, _, Dom', Val', uSlot, ss, _, _, .bvar _ _ Γ0 i A u hlu _, p, δ, acts, s, ρ' =>
      BvarGate μ' (levelIsZero (stageMap μ' (steps ss) u)) uSlot k (Skels.appLevel (steps ss) u)
        (walkSite s i) (bwalkAtL k Dom' Val' ss i A Γ0 hlu p.inv p.run)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .const .., _, _, _, _, _ => True
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .pi _ _ _ A u _ _ hA hB, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext hA p δ acts s ρ' ∧
      BodyAnswers hW ι ιenv tbl μ' hext
        hB (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
          (onDecl_assumption (steps ss) A).symm)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: δ)
        (binderActs (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) acts)
        (sitesShift (.assumption (Skels.app (steps ss) A)) (.assumption A) s)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: ρ')
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .lam _ _ _ A u _ _ _ _ hbody _, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext
        hbody (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
          (onDecl_assumption (steps ss) A).symm)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: δ)
        (binderActs (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) acts)
        (sitesShift (.assumption (Skels.app (steps ss) A)) (.assumption A) s)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: ρ')
  | _, hext, _, _, _, _, _, _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext hf p δ acts s ρ' ∧
      BodyAnswers hW ι ιenv tbl μ' hext ha p δ acts s ρ'
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .letE _ _ _ A _ value _ _ _ _ hv hb _, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext hv p δ acts s ρ' ∧
      BodyAnswers hW ι ιenv tbl μ' hext
        hb (packLUnder p (.letBinding A value)
          (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
          (onDecl_let (steps ss) A value).symm)
        (letDisp (hv.eps (stageMap μ' (steps ss)) δ) :: δ) acts
        (sitesShift (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
          (.letBinding A value) s)
        (letDisp ((tyAtLet hW ι ιenv hext p hv).eps μ' ρ') :: ρ')
  | _, hext, _, _, _, _, _, _, _, _, _, _, _, .lit _ _ _ _ _ hexp, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext hexp p δ acts s ρ'
  | _, hext, _, _, _, _, _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext h p δ acts s ρ'
  | _, hext, _, _, _, _, _, _, _, _, _, _, _, .wk _ _ _ _ _ d c Di, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext Di (packLConsWk c d p) (removeAt δ c) (wkActs δ c acts)
        (.wk c d s) ρ'
  | _, hext, _, _, k, _, _, Dom', Val', _, ss, _, _, .esub _ _ Γ0 _ _ t v j u Di hget hv hvT, p,
      δ, acts, s, ρ' =>
      PBit (stageMap μ' (steps ss)) δ hv hvT ∧
      BodyAnswers hW ι ιenv tbl μ' hext hv p δ acts s ρ' ∧
      BodyAnswers hW ι ιenv tbl μ' hext
        Di (packLEsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p)
        (insertDisp (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) j δ)
        (esubActs (levelIsZero (stageMap μ' (steps ss) u)) (countKeep (δ.take j))
          (hv.eps (stageMap μ' (steps ss)) δ) acts)
        (.esub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
          (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) ρ'
  | _, hext, _, _, k, _, _, Dom', Val', _, ss, _, _, .lsub _ _ Γ0 _ _ t v j u Di hget hv hvT, p,
      δ, acts, s, ρ' =>
      PBit (stageMap μ' (steps ss)) δ hv hvT ∧
      (hv.eps (stageMap μ' (steps ss)) δ ≠ .star →
        AvoidPrefix (countKeep (δ.take j)) 0 (hv.eps (stageMap μ' (steps ss)) δ)) ∧
      BodyAnswers hW ι ιenv tbl μ' hext hv p δ acts s ρ' ∧
      BodyAnswers hW ι ιenv tbl μ' hext
        Di (packLLsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p)
        (insertDisp (lsubDisp (countKeep (δ.take j)) (hv.eps (stageMap μ' (steps ss)) δ)) j δ) acts
        (.lsub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
          (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) ρ'
  | _, hext, nIn, _, _, _, _, _, _, _, _, _, _, .linst _ a _ _ _ _ ls hls hlen Di, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' hext Di (packLLinst ls a nIn hls hlen p) δ acts
        (.linst ls a nIn hls hlen s) ρ'
  | _, hext, _, _, _, _, _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ hext' Di, p, δ, acts, s, ρ' =>
      BodyAnswers hW ι ιenv tbl μ' (envExt_trans hext' hext) Di p δ acts s ρ'
  | _, hext, _, _, k, _, _, Dom', Val', _, ss, _, _, .cctx _ _ Γ0 _ _ A A' _ Dinner hA, p, δ, acts, s, ρ' =>
      let pA := packLWk (.assumption A') p
      let hc0 := cvAtLet hW ι ιenv hext pA hA
      let hc1 := cvToSort hc0
      let hOld := toSort hc0.dl
      let hNew := toSort hc0.dr
      let flipped :=
        CvP.symm E n
          (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ0)))
          (Skels.app (steps ss) (lift 0 1 A))
          (Skels.app (steps ss) (lift 0 1 A'))
          (.sort (Skels.appLevel (steps ss) _))
          hc1 hNew hOld
      BodyAnswers hW ι ιenv tbl μ' hext Dinner (packLCctx flipped p) δ acts
        (.cctx 0 A' (Skels.app (steps ss) (lift 0 1 A')) (Skels.app (steps ss) (lift 0 1 A))
          (Skels.appLevel (steps ss) _)
          (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ0))) flipped s) ρ'

/-! ## §4 the induction -/

/-- The LetBridge induction (Part III "Induction"). -/
theorem letBridge {E : ResolvedEnv} {n : Nat} {tbl : List CRule} (hcl : TableClosed tbl)
    (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (μ' : Level → Level) :
    ∀ {Ei : ResolvedEnv} (hext : EnvExt Ei E)
      {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
      {ss : List (PStep E n)} {e T : Expr Nat}
      (D : TyP Ei nIn Γ e T) (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ)
      (δ : List Disp) (acts : List EAct) (s : Sites ss) (ρ' : List Disp),
      D.AssumpPref → DisplayFits Γ δ → EActsNonStar acts →
      TraceInv tbl μ' ρ' k Dom' Val' ss Γ δ acts p.inv p.run s →
      BodyAnswers hW ι ιenv tbl μ' hext D p δ acts s ρ' →
      Rel tbl (applyActs acts (D.eps (stageMap μ' (steps ss)) δ))
        ((tyAtLet hW ι ιenv hext p D).eps μ' ρ')
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .sort _ _ _ l k' h, p, δ, acts, s, ρ', _, _, _, _, _ => by
      show Rel tbl (applyActs acts (.sort (stageMap μ' (steps ss) l)))
        ((tySort l k' h (steps ss)).eps μ' ρ')
      rw [applyActs_sort, eps_tySort]
      exact Rel.refl tbl _
  | _, hext, _, _, k, _, _, Dom', Val', uSlot, ss, _, _, .bvar _ _ Γ0 i A u hlu hA, p, δ, acts, s, ρ',
      _, _, _, htr, hans => by
      show Rel tbl (applyActs acts ((TyP.bvar _ _ Γ0 i A u hlu hA).eps (stageMap μ' (steps ss)) δ))
        ((finishBvarL p.get p.slotTy (toSort (tyAtLet hW ι ιenv hext p hA))
          (bwalkAtL k Dom' Val' ss i A Γ0 hlu p.inv p.run)).eps μ' ρ')
      rw [eps_bvar_gateOut, applyActs_gateOut]
      exact rel_finishBvarL p.get p.slotTy _ _ _ rfl (htr i A hlu) hans
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .const _ _ _ r ls ls₀ m u hres hlen hwf hls hT, p,
      δ, acts, s, ρ', _, _, _, _, _ => by
      show Rel tbl (applyActs acts
          ((TyP.const _ _ _ r ls ls₀ m u hres hlen hwf hls hT).eps (stageMap μ' (steps ss)) δ))
        ((tyConst hW (hext r m hres) hlen hwf hls ss p.fuel
          (toSort (tyAtLet hW ι ιenv hext p hT))).eps μ' ρ')
      rw [eps_const_gateOut, applyActs_gateOut, applyActs_const, eps_tyConst]
      exact Rel.refl tbl _
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .pi _ _ _ A u B v hA hB, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ihA := letBridge hcl hW ι ιenv μ' hext hA p δ acts s ρ' hAP.1 hfit hns htr hans.1
      have ihB := letBridge hcl hW ι ιenv μ' hext
        hB (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
          (onDecl_assumption (steps ss) A).symm)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: δ)
        (binderActs (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) acts)
        (sitesShift (.assumption (Skels.app (steps ss) A)) (.assumption A) s)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: ρ')
        hAP.2 (displayFits_binderDisp A _ hfit) (eActsNonStar_binderActs _ hns)
        (traceInv_under hcl htr _ _ _ _ _ (binderRel_binderDisp tbl acts _)) hans.2
      rw [stageMap_shift] at ihB
      show Rel tbl (applyActs acts ((TyP.pi _ _ _ A u B v hA hB).eps (stageMap μ' (steps ss)) δ))
        ((tyPi A B u v (steps ss) (toSort (tyAtLet hW ι ιenv hext p hA))
          (toSort (moveUnderL (onDecl_assumption (steps ss) A).symm
            (tyAtLet hW ι ιenv hext
              (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
                (onDecl_assumption (steps ss) A).symm) hB)))).eps μ' ρ')
      rw [eps_pi_bit, eps_tyPi, eps_toSort, eps_toSort, eps_moveUnderL, applyActs_pi,
        applyActs_shift_piSlot]
      exact rel_pi ihA (rel_piSlot hcl _ ihB)
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .lam _ _ _ A u body B v hA hbody hB, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ih := letBridge hcl hW ι ιenv μ' hext
        hbody (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
          (onDecl_assumption (steps ss) A).symm)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: δ)
        (binderActs (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) acts)
        (sitesShift (.assumption (Skels.app (steps ss) A)) (.assumption A) s)
        (binderDisp (levelIsZero (stageMap μ' (steps ss) u)) :: ρ')
        hAP.2.1 (displayFits_binderDisp A _ hfit) (eActsNonStar_binderActs _ hns)
        (traceInv_under hcl htr _ _ _ _ _ (binderRel_binderDisp tbl acts _)) hans
      rw [stageMap_shift] at ih
      show Rel tbl
        (applyActs acts ((TyP.lam _ _ _ A u body B v hA hbody hB).eps (stageMap μ' (steps ss)) δ))
        ((tyLam A body B u v (steps ss) (toSort (tyAtLet hW ι ιenv hext p hA))
          (moveUnderL (onDecl_assumption (steps ss) A).symm
            (tyAtLet hW ι ιenv hext
              (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
                (onDecl_assumption (steps ss) A).symm) hbody))
          (toSort (moveUnderL (onDecl_assumption (steps ss) A).symm
            (tyAtLet hW ι ιenv hext
              (packLUnder p (.assumption A) (.assumption (Skels.app (steps ss) A))
                (onDecl_assumption (steps ss) A).symm) hB)))).eps μ' ρ')
      rw [eps_lam_clause, eps_tyLam, eps_moveUnderL, applyActs_lamErasure _ _ hns,
        ← binderActs_binderDisp]
      exact rel_lamErasure _ ih
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .app _ _ _ f a A B w hf ha hT, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ihf := letBridge hcl hW ι ιenv μ' hext hf p δ acts s ρ' hAP.1 hfit hns htr hans.1
      have iha := letBridge hcl hW ι ιenv μ' hext ha p δ acts s ρ' hAP.2.1 hfit hns htr hans.2
      show Rel tbl
        (applyActs acts ((TyP.app _ _ _ f a A B w hf ha hT).eps (stageMap μ' (steps ss)) δ))
        ((tyApp f a A B w (steps ss) (toPi (tyAtLet hW ι ιenv hext p hf))
          (tyAtLet hW ι ιenv hext p ha) (toSort (tyAtLet hW ι ιenv hext p hT))).eps μ' ρ')
      rw [eps_app_appClause, eps_tyApp, eps_toPi, applyActs_appClause _ hns]
      exact rel_appClause ihf iha
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .letE _ _ _ A u value B body w hA hv hb hT, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ihv := letBridge hcl hW ι ιenv μ' hext hv p δ acts s ρ' hAP.2.1 hfit hns htr hans.1
      have ihb := letBridge hcl hW ι ιenv μ' hext
        hb (packLUnder p (.letBinding A value)
          (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
          (onDecl_let (steps ss) A value).symm)
        (letDisp (hv.eps (stageMap μ' (steps ss)) δ) :: δ) acts
        (sitesShift (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
          (.letBinding A value) s)
        (letDisp ((tyAtLet hW ι ιenv hext p hv).eps μ' ρ') :: ρ')
        hAP.2.2.1 (displayFits_letDisp A value _ hfit) hns
        (by
          have := traceInv_under hcl htr (.letBinding A value)
            (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
            (onDecl_let (steps ss) A value).symm _ _ (binderRel_letDisp hns ihv)
          rwa [binderActs_letDisp] at this) hans.2
      rw [stageMap_shift] at ihb
      rw [tyAtLet_letE_eps, let_eps_eq]
      exact ihb
  | _, hext, _, _, _, _, _, _, _, _, ss, _, T, .lit _ _ _ t _ hexp, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ih := letBridge hcl hW ι ιenv μ' hext hexp p δ acts s ρ' hAP hfit hns htr hans
      show Rel tbl (applyActs acts ((TyP.lit _ _ _ t T hexp).eps (stageMap μ' (steps ss)) δ))
        ((tyLit t T (steps ss) (tyAtLet hW ι ιenv hext p hexp)).eps μ' ρ')
      rw [eps_lit, eps_tyLit]
      exact ih
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .conv _ _ _ e A B u h hc, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ih := letBridge hcl hW ι ιenv μ' hext h p δ acts s ρ' hAP.1 hfit hns htr hans
      show Rel tbl (applyActs acts ((TyP.conv _ _ _ e A B u h hc).eps (stageMap μ' (steps ss)) δ))
        ((TyP.conv E n _ _ _ _ (Skels.appLevel (steps ss) _)
          (tyAtLet hW ι ιenv hext p h) (cvToSort (cvAtLet hW ι ιenv hext p hc))).eps μ' ρ')
      rw [eps_conv, eps_conv]
      exact ih
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .wk _ _ Γ0 e0 A0 d c Di, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ih := letBridge hcl hW ι ιenv μ' hext Di (packLConsWk c d p) (removeAt δ c)
        (wkActs δ c acts) (.wk c d s) ρ' hAP.2 (displayFits_removeAt d c hfit)
        (eActsNonStar_wkActs δ c hns) (traceInv_wk c d htr hfit hAP.1) hans
      rw [applyActs_eps_wk]
      exact ih
  | _, hext, _, _, k, _, _, Dom', Val', _, ss, _, _, .esub _ _ Γ0 e0 A0 t v j u Di hget hv hvT, p,
      δ, acts, s, ρ', hAP, hfit, hns, htr, hans => by
      obtain ⟨hpb, hansv, hansD⟩ := hans
      have ihv := letBridge hcl hW ι ιenv μ' hext hv p δ acts s ρ' hAP.2.2.1 hfit hns htr hansv
      have hne : levelIsZero (stageMap μ' (steps ss) u) = false →
          hv.eps (stageMap μ' (steps ss)) δ ≠ .star := fun hb hs => by
        have hs' : levelIsZero (stageMap μ' (steps ss) u) = true := Iff.mp hpb hs
        rw [hs'] at hb; cases hb
      have htr' : TraceInv tbl μ' ρ' k Dom' Val'
          (.esub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
            ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
            (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
            (tyAtLet hW ι ιenv hext p hv) :: ss) Γ0
          (insertDisp (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) j δ)
          (esubActs (levelIsZero (stageMap μ' (steps ss) u)) (countKeep (δ.take j))
            (hv.eps (stageMap μ' (steps ss)) δ) acts)
          (packLEsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p).inv
          (packLEsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p).run
          (.esub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
            ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
            (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
            (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) := by
        cases hb : levelIsZero (stageMap μ' (steps ss) u)
        · exact traceInv_esub_keep _ _ rfl rfl rfl rfl htr hfit hAP.1 hns _ u _ hpb hb ihv
        · exact traceInv_esub_drop _ _ rfl rfl rfl rfl htr hfit hns _ u _ hpb hb ihv
      have ih := letBridge hcl hW ι ιenv μ' hext
        Di (packLEsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p)
        (insertDisp (binderDisp (levelIsZero (stageMap μ' (steps ss) u))) j δ)
        (esubActs (levelIsZero (stageMap μ' (steps ss) u)) (countKeep (δ.take j))
          (hv.eps (stageMap μ' (steps ss)) δ) acts)
        (.esub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
          (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) ρ'
        hAP.2.1
        (displayFits_insertDisp_assump v j ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) hfit _
          (binderDisp_shape _))
        (eActsNonStar_esubActs hns hne) htr' hansD
      rw [applyActs_eps_esub]
      exact ih
  | _, hext, _, _, k, _, _, Dom', Val', _, ss, _, _, .lsub _ _ Γ0 e0 A0 t v j u Di hget hv hvT, p,
      δ, acts, s, ρ', hAP, hfit, hns, htr, hans => by
      obtain ⟨hpb, hscope, hansv, hansD⟩ := hans
      have ihv := letBridge hcl hW ι ιenv μ' hext hv p δ acts s ρ' hAP.2.2.1 hfit hns htr hansv
      have htr' := traceInv_lsub (k := k) (Dom' := Dom') (Val' := Val')
        ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) rfl rfl rfl rfl
        htr hfit hns (stageMap μ' (steps ss)) u _ hpb hscope ihv
      have ih := letBridge hcl hW ι ιenv μ' hext
        Di (packLLsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) (tyAtLet hW ι ιenv hext p hv) p)
        (insertDisp (lsubDisp (countKeep (δ.take j)) (hv.eps (stageMap μ' (steps ss)) δ)) j δ) acts
        (.lsub j v t Γ0 (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))
          (tyAtLet hW ι ιenv hext p hv) (stageMap μ' (steps ss)) u s) ρ'
        hAP.2.1
        (displayFits_insertDisp_let v j ((List.get?_eq_getElem? Γ0 j).symm ▸ hget) hfit _
          (lsubDisp_shape _ _))
        hns htr' hansD
      rw [lsub_eps_eq]
      exact ih
  | _, hext, nIn, _, _, _, _, _, _, _, ss, _, _, .linst _ a _ Γ0 e0 A0 ls hls hlen Di, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ih := letBridge hcl hW ι ιenv μ' hext Di (packLLinst ls a nIn hls hlen p) δ acts
        (.linst ls a nIn hls hlen s) ρ' hAP (displayFits_of_instLvlsCtx ls Γ0 hfit) hns
        (traceInv_linst ls a nIn hls hlen htr) hans
      rw [eps_linst]
      exact ih
  | _, hext, _, _, _, _, _, _, _, _, ss, _, _, .ewk E₀ _ _ _ _ _ hext' Di, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      have ih := letBridge hcl hW ι ιenv μ' (envExt_trans hext' hext) Di p δ acts s ρ' hAP hfit hns
        htr hans
      rw [eps_ewk]
      exact ih
  | _, hext, _, _, k, _, _, Dom', Val', _, ss, _, _, .cctx _ _ Γ0 e0 T0 A A' u Dinner hA, p, δ, acts, s, ρ',
      hAP, hfit, hns, htr, hans => by
      simp only [BodyAnswers] at hans
      have ih := letBridge hcl hW ι ιenv μ' hext Dinner _ δ acts _ ρ'
        hAP.1 (displayFits_setAssump A 0 hfit ⟨A', rfl⟩) hns
        (traceInv_cctx (Γ := .assumption A :: Γ0) 0 A' _ _ _ _ A rfl rfl rfl rfl htr) hans
      rw [eps_cctx]
      exact ih

end Rcic.Syn

#print axioms Rcic.Syn.stageMap_shift
#print axioms Rcic.Syn.applyActs_eps_esub
#print axioms Rcic.Syn.applyActs_eps_wk
#print axioms Rcic.Syn.traceInv_lsub
#print axioms Rcic.Syn.BodyAnswers
#print axioms Rcic.Syn.letBridge
