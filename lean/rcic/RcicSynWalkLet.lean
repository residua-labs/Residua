import rcic.RcicSynPiInv

/-!
# RcicSynWalkLet — transport walk over a `.letBinding` slot (step 4c `hlet` discharge)

`RcicSynWalk.tyAt`/`cvAt` transport a `TyP`/`CvP` through a transport skeleton
while rewriting one `.assumption` slot (`setAssump k Dom'`). `letRightP`
(`RcicSynEnrich`) needs the same transport over a `.letBinding` slot — that is
`LetCtxConvP`, the `hlet` premise of the enriched sort-uniqueness theorem.

This file is the let-slot twin: `setLetB` replaces the `.letBinding` at `k`,
`RunL`/`PackL` thread the new type `Dom'` AND the new value `Val'`, and
`tyAtLet`/`cvAtLet` replay the walk. The only arm that gains a case is the
`zetaLocal` slot-hit: under `.assumption` it is impossible
(`lookupValue_assumption_none`); under `.letBinding` it is real and emits
`zetaLocal` at the new value, then `tyConv`/`trans` along the lifted slot
conversions.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `setLetB` — replace the `.letBinding` at position `k` -/

/-- Replace the let-binding at position `k`. A short context is left unchanged.
    The list is matched first, so `setLetB k A v []` reduces while `k` is a variable. -/
def setLetB (k : Nat) (A v : Expr Nat) : LCtx → LCtx
  | [] => []
  | d :: Γ =>
    match k with
    | 0 => .letBinding A v :: Γ
    | k + 1 => d :: setLetB k A v Γ

theorem setLetB_zero (A v : Expr Nat) (d : LocalDecl) (Γ : LCtx) :
    setLetB 0 A v (d :: Γ) = .letBinding A v :: Γ := rfl

theorem setLetB_succ (k : Nat) (A v : Expr Nat) (d : LocalDecl) (Γ : LCtx) :
    setLetB (k + 1) A v (d :: Γ) = d :: setLetB k A v Γ := rfl

theorem setLetB_nil (k : Nat) (A v : Expr Nat) : setLetB k A v [] = [] := by
  cases k <;> rfl

theorem length_setLetB (Dom' Val' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → (setLetB k Dom' Val' Γ).length = Γ.length
  | [], k => by rw [setLetB_nil]
  | _ :: Γ, 0 => by rw [setLetB_zero]; rfl
  | _ :: Γ, k + 1 => by
      rw [setLetB_succ, List.length_cons, List.length_cons]
      exact congrArg Nat.succ (length_setLetB Dom' Val' Γ k)

theorem drop_setLetB (Dom' Val' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → (setLetB k Dom' Val' Γ).drop (k + 1) = Γ.drop (k + 1)
  | [], k => by rw [setLetB_nil]
  | _ :: Γ, 0 => by rw [setLetB_zero, List.drop_one]; rfl
  | _ :: Γ, k + 1 => by
      rw [setLetB_succ, List.drop_succ_cons, List.drop_succ_cons]
      exact drop_setLetB Dom' Val' Γ k

/-- An index other than `k` reads the same declaration. -/
theorem get?_setLetB_ne (Dom' Val' : Expr Nat) :
    (Γ : LCtx) → (k i : Nat) → i ≠ k → (setLetB k Dom' Val' Γ).get? i = Γ.get? i
  | [], _, i, _ => by rw [setLetB_nil]
  | _ :: _, 0, 0, hne => absurd rfl hne
  | _ :: Γ, 0, i + 1, _ => by
      rw [setLetB_zero, List.get?_cons_succ, List.get?_cons_succ]
  | _ :: _, k + 1, 0, _ => by
      rw [setLetB_succ, List.get?_cons_zero, List.get?_cons_zero]
  | _ :: Γ, k + 1, i + 1, hne => by
      rw [setLetB_succ, List.get?_cons_succ, List.get?_cons_succ]
      exact get?_setLetB_ne Dom' Val' Γ k i (fun h => hne (congrArg Nat.succ h))

theorem lookupType_setLetB_ne {k i : Nat} {A Dom' Val' : Expr Nat} {Γ : LCtx}
    (hne : i ≠ k) (h : lookupType Γ i = some A) :
    lookupType (setLetB k Dom' Val' Γ) i = some A := by
  unfold lookupType at h ⊢
  rw [get?_setLetB_ne Dom' Val' Γ k i hne]
  exact h

theorem lookupValue_setLetB_ne {k i : Nat} {v Dom' Val' : Expr Nat} {Γ : LCtx}
    (hne : i ≠ k) (h : lookupValue Γ i = some v) :
    lookupValue (setLetB k Dom' Val' Γ) i = some v := by
  unfold lookupValue at h ⊢
  rw [get?_setLetB_ne Dom' Val' Γ k i hne]
  exact h

/-- The replaced slot's lookup-type is the new stored type, lifted by `k + 1`. -/
theorem lookupType_setLetB_hit (Dom' Val' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → {Dom Val : Expr Nat} →
      Γ.get? k = some (.letBinding Dom Val) →
        lookupType (setLetB k Dom' Val' Γ) k = some (lift 0 (k + 1) Dom')
  | _ :: _, 0, _, _, _ => by
      rw [setLetB_zero, lookupType, List.get?_cons_zero]
  | d :: Γ, k + 1, Dom, Val, h => by
      rw [List.get?_cons_succ] at h
      rw [setLetB_succ, lookupType_cons_succ,
        lookupType_setLetB_hit Dom' Val' Γ k h, Option.map_some']
      exact congrArg some (lift_lift_merge 1 (k + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) Dom')
  | [], _, _, _, h => by rw [List.get?_nil] at h; cases h

/-- The replaced slot's lookup-value is the new stored value, lifted by `k + 1`. -/
theorem lookupValue_setLetB_hit (Dom' Val' : Expr Nat) :
    (Γ : LCtx) → (k : Nat) → {Dom Val : Expr Nat} →
      Γ.get? k = some (.letBinding Dom Val) →
        lookupValue (setLetB k Dom' Val' Γ) k = some (lift 0 (k + 1) Val')
  | _ :: _, 0, _, _, _ => by
      rw [setLetB_zero, lookupValue, List.get?_cons_zero]
  | d :: Γ, k + 1, Dom, Val, h => by
      rw [List.get?_cons_succ] at h
      rw [setLetB_succ, lookupValue_cons_succ,
        lookupValue_setLetB_hit Dom' Val' Γ k h, Option.map_some']
      exact congrArg some (lift_lift_merge 1 (k + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) Val')
  | [], _, _, _, h => by rw [List.get?_nil] at h; cases h

/-- `lookupType` at a `setLetB` slot index `i`, given the slot is a `.letBinding`
    there already. Used by `bwalkAtLet`'s `.cctx` arm. -/
theorem lookupType_setLetB_at (Dom' Val' : Expr Nat) :
    (Γ : LCtx) → (i : Nat) → {A : Expr Nat} → lookupType Γ i = some A →
      lookupType (setLetB i Dom' Val' Γ) i = some (lift 0 (i + 1) Dom')
  | [], _, _, h => by
      unfold lookupType at h
      rw [List.get?_nil] at h
      cases h
  | _ :: _, 0, _, _ => by
      rw [setLetB_zero, lookupType, List.get?_cons_zero]
  | d :: Γ, i + 1, _, h => by
      rw [lookupType_cons_succ] at h
      cases hlu : lookupType Γ i with
      | none =>
          rw [hlu, Option.map_none'] at h
          cases h
      | some _ =>
          rw [hlu, Option.map_some'] at h
          cases h
          rw [setLetB_succ, lookupType_cons_succ,
            lookupType_setLetB_at Dom' Val' Γ i hlu, Option.map_some']
          exact congrArg some
            (lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) Dom')

/-- `c < k`: the insertion is newer than the target, so the target's index
    shifts by one and `setLetB` commutes with `insertAt`. -/
theorem setLetB_insertAt_gt (d : LocalDecl) (Dom' Val' : Expr Nat) :
    (c k : Nat) → (Γ : LCtx) → c < k →
      setLetB k Dom' Val' (insertAt d c Γ) = insertAt d c (setLetB (k - 1) Dom' Val' Γ)
  | 0, 0, _, hck => absurd hck (Nat.lt_irrefl 0)
  | 0, k + 1, Γ, _ => by
      simp only [insertAt_zero, setLetB_succ, Nat.add_sub_cancel]
  | c + 1, 0, _, hck => absurd hck (Nat.not_lt_zero (c + 1))
  | c + 1, k + 1, [], _ => by
      have hL : setLetB (k + 1) Dom' Val' (insertAt d (c + 1) []) = [d] := by
        rw [show insertAt d (c + 1) ([] : LCtx) = [d] from rfl, setLetB_succ, setLetB_nil]
      have hR : insertAt d (c + 1) (setLetB k Dom' Val' []) = [d] := by
        rw [setLetB_nil, show insertAt d (c + 1) ([] : LCtx) = [d] from rfl]
      exact hL.trans hR.symm
  | c + 1, k + 1, x :: Γ, hck => by
      have hk : c < k := Nat.lt_of_succ_lt_succ hck
      have hkpos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le c) hk
      have hR : insertAt d (c + 1) (setLetB k Dom' Val' (x :: Γ)) =
          liftDecl c x :: insertAt d c (setLetB (k - 1) Dom' Val' Γ) := by
        have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)).symm
        rw [hk1, setLetB_succ, insertAt_succ_cons, Nat.add_sub_cancel]
      rw [show (k + 1) - 1 = k from Nat.add_sub_cancel k 1]
      rw [insertAt_succ_cons, setLetB_succ, setLetB_insertAt_gt d Dom' Val' c k Γ hk, hR]

/-- `c = k` and the context is long enough for the insertion to land at `c`:
    replacing that slot is `insertAt` of the new let-binding. -/
theorem setLetB_insertAt_eq (Dom' Val' : Expr Nat) (d : LocalDecl) :
    (c : Nat) → (Γ : LCtx) → c ≤ Γ.length →
      setLetB c Dom' Val' (insertAt d c Γ) = insertAt (.letBinding Dom' Val') c Γ
  | 0, Γ, _ => by simp only [insertAt_zero, setLetB_zero]
  | c + 1, [], hle => absurd hle (Nat.not_succ_le_zero c)
  | c + 1, x :: Γ, hle => by
      simp only [insertAt_succ_cons, setLetB_succ, List.length_cons] at *
      exact congrArg (liftDecl c x :: ·) (setLetB_insertAt_eq Dom' Val' d c Γ (Nat.le_of_succ_le_succ hle))

/-! ## §2 `RunL` — the let-slot thread through the skeleton -/

variable {E : ResolvedEnv} {n : Nat}

/-- `RunL` threads the let-slot's replacement `letBinding Dom' Val'` through the
    recorded steps. Identical to `Run` except `setLetB k Dom' Val'` replaces
    `setAssump k Dom'`; the `.cctx` arm's own slot stays `.assumption`. -/
inductive RunL (k : Nat) (Dom' Val' : Expr Nat) {E : ResolvedEnv} {n : Nat} :
    List (PStep E n) → LCtx → Type where
  | nil {Γ : LCtx} : RunL k Dom' Val' [] Γ
  | wk {Γ : LCtx} (c : Nat) (d : LocalDecl) {ss : List (PStep E n)}
      (h : RunL k Dom' Val' ss (insertAt d c Γ)) : RunL k Dom' Val' (.wk c d :: ss) Γ
  | esub {Γ : LCtx} {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx}
      {hget : Γe.get? j = some (.assumption t)} {repl replT : Expr Nat}
      {hv : TyP E n Γr repl replT} {ss : List (PStep E n)}
      (hΓ : Γ = Γe)
      (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (h : RunL k Dom' Val' ss (substRemove v j Γ)) :
      RunL k Dom' Val' (.esub j v t Γe Γr hget repl replT hv :: ss) Γ
  | lsub {Γ : LCtx} {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx}
      {hget : Γe.get? j = some (.letBinding t v)} {repl replT : Expr Nat}
      {hv : TyP E n Γr repl replT} {ss : List (PStep E n)}
      (hΓ : Γ = Γe)
      (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (h : RunL k Dom' Val' ss (substRemove v j Γ)) :
      RunL k Dom' Val' (.lsub j v t Γe Γr hget repl replT hv :: ss) Γ
  | linst {Γ : LCtx} (ls : List Level) (a nStep : Nat)
      (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
      {ss : List (PStep E n)}
      (h : RunL k Dom' Val' ss (instLvlsCtx ls Γ)) :
      RunL k Dom' Val' (.linst ls a nStep hls hlen :: ss) Γ
  | cctx {Γ : LCtx} (p : Nat) (Askel newTy oldTy : Expr Nat) (u : Level) {Γr : LCtx}
      {hc : CvP E n Γr newTy oldTy (.sort u)} {ss : List (PStep E n)}
      (Aold : Expr Nat)
      (hdec : Γ.get? p = some (.assumption Aold))
      (hnew : newTy = Skels.app (steps ss) (lift 0 (p + 1) Askel))
      (hold : oldTy = Skels.app (steps ss) (lift 0 (p + 1) Aold))
      (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (setAssump p Askel Γ)))
      (h : RunL k Dom' Val' ss (setAssump p Askel Γ)) :
      RunL k Dom' Val' (.cctx p Askel newTy oldTy u Γr hc :: ss) Γ

/-! ## §3 pushing `RunL` under one binder -/

theorem shiftL_lsub_hctx {n k j : Nat} {Dom' Val' v : Expr Nat}
    {dLocal dFinal : LocalDecl} {Γ Γr Γe : LCtx} {t repl replT : Expr Nat}
    {hget : Γe.get? j = some (.letBinding t v)} {hv : TyP E n Γr repl replT}
    {ss : List (PStep E n)}
    (hd : dFinal =
      Skels.onDecl (steps (.lsub j v t Γe Γr hget repl replT hv :: ss)) dLocal)
    (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ))) :
    insertAt dFinal 0 Γr =
      setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
          (substRemove v (j + 1) (dLocal :: Γ))) := by
  rw [hctx, insertAt_zero, substRemove_succ_cons, steps_shiftAll, ctx_shift, setLetB_succ]
  refine congrArg (fun d => d :: setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ))) ?_
  simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd

theorem shiftL_esub_hctx {n k j : Nat} {Dom' Val' v : Expr Nat}
    {dLocal dFinal : LocalDecl} {Γ Γr Γe : LCtx} {t repl replT : Expr Nat}
    {hget : Γe.get? j = some (.assumption t)} {hv : TyP E n Γr repl replT}
    {ss : List (PStep E n)}
    (hd : dFinal =
      Skels.onDecl (steps (.esub j v t Γe Γr hget repl replT hv :: ss)) dLocal)
    (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ))) :
    insertAt dFinal 0 Γr =
      setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
          (substRemove v (j + 1) (dLocal :: Γ))) := by
  rw [hctx, insertAt_zero, substRemove_succ_cons, steps_shiftAll, ctx_shift, setLetB_succ]
  refine congrArg (fun d => d :: setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ))) ?_
  simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd

theorem shiftL_cctx_hctx {n k p : Nat} {Dom' Val' Askel newTy oldTy : Expr Nat} {u : Level}
    {dLocal dFinal : LocalDecl} {Γ Γr : LCtx} {hc : CvP E n Γr newTy oldTy (.sort u)}
    {ss : List (PStep E n)}
    (hd : dFinal =
      Skels.onDecl (steps (.cctx p Askel newTy oldTy u Γr hc :: ss)) dLocal)
    (hctx : Γr =
      setLetB k Dom' Val' (Skels.ctx (steps ss) (setAssump p Askel Γ))) :
    insertAt dFinal 0 Γr =
      setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll (Skel.onDecl (.cctx p Askel) dLocal) dFinal ss))
          (setAssump (p + 1) Askel (dLocal :: Γ))) := by
  rw [hctx, insertAt_zero, setAssump_succ, steps_shiftAll, ctx_shift, setLetB_succ]
  refine congrArg
    (fun d => d :: setLetB k Dom' Val' (Skels.ctx (steps ss) (setAssump p Askel Γ))) ?_
  simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd

def runL_shift {n : Nat} (k : Nat) (Dom' Val' : Expr Nat) (dLocal dFinal : LocalDecl) :
    (ss : List (PStep E n)) → (Γ : LCtx) →
      dFinal = Skels.onDecl (steps ss) dLocal →
      RunL k Dom' Val' ss Γ →
      RunL (k + 1) Dom' Val' (shiftAll dLocal dFinal ss) (dLocal :: Γ)
  | [], _, _, .nil => .nil
  | .wk c decl :: ss, Γ, hd, .wk _ _ h =>
      .wk (c + 1) decl
        (runL_shift k Dom' Val' (liftDecl c dLocal) dFinal ss (insertAt decl c Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .linst ls a nStep hls hlen :: ss, Γ, hd, .linst _ _ _ _ _ h =>
      .linst ls a nStep hls hlen
        (runL_shift k Dom' Val' (instLvlsDecl ls dLocal) dFinal ss (instLvlsCtx ls Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .esub j v t Γe Γr hget repl replT hv :: ss, Γ, hd, .esub hΓ hctx h =>
      .esub (congrArg (List.cons dLocal) hΓ) (shiftL_esub_hctx hd hctx)
        (runL_shift k Dom' Val' (instDecl j v dLocal) dFinal ss (substRemove v j Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .lsub j v t Γe Γr hget repl replT hv :: ss, Γ, hd, .lsub hΓ hctx h =>
      .lsub (congrArg (List.cons dLocal) hΓ) (shiftL_lsub_hctx hd hctx)
        (runL_shift k Dom' Val' (instDecl j v dLocal) dFinal ss (substRemove v j Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .cctx p Askel newTy oldTy u Γr hc :: ss, Γ, hd,
      .cctx _ _ _ _ _ Aold hdec hnew hold hctx h =>
      .cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u Aold
        (get?_cons_succ_assumption (d := dLocal) hdec)
        (shift_cctx_term dLocal dFinal hnew)
        (shift_cctx_term dLocal dFinal hold)
        (shiftL_cctx_hctx hd hctx)
        (runL_shift k Dom' Val' dLocal dFinal ss (setAssump p Askel Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)

/-! ## §4 `PackL` — the let-slot pack -/

/-- The let-slot pack. `get` pins the transformed slot to `.letBinding Dom Val`;
    `slotTy` is the domain conversion `Dom → Dom'` and `slotVal` the value
    conversion `Val → Val'`, both under the transformed tail. -/
structure PackL (E : ResolvedEnv) (n k : Nat) (Dom Val Dom' Val' : Expr Nat) (uSlot : Level)
    (nIn : Nat) (ss : List (PStep E n)) (Γ : LCtx) : Type where
  fuel : FuelRel ss nIn
  inv : EsInv ss
  run : RunL k Dom' Val' ss Γ
  get : (Skels.ctx (steps ss) Γ).get? k = some (.letBinding Dom Val)
  slotTy : CvP E n ((Skels.ctx (steps ss) Γ).drop (k + 1)) Dom Dom' (.sort uSlot)
  slotVal : CvP E n ((Skels.ctx (steps ss) Γ).drop (k + 1)) Val Val' Dom

def packLWk {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} (d : LocalDecl)
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (insertAt d 0 Γ)) :
    PackL E n k Dom Val Dom' Val' uSlot nIn (.wk 0 d :: ss) Γ where
  fuel := .wk 0 d p.fuel
  inv := .wk 0 d p.inv
  run := .wk 0 d p.run
  get := p.get
  slotTy := p.slotTy
  slotVal := p.slotVal

def packLConsWk {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} (c : Nat) (d : LocalDecl)
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (insertAt d c Γ)) :
    PackL E n k Dom Val Dom' Val' uSlot nIn (.wk c d :: ss) Γ where
  fuel := .wk c d p.fuel
  inv := .wk c d p.inv
  run := .wk c d p.run
  get := p.get
  slotTy := p.slotTy
  slotVal := p.slotVal

def packLLinst {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {Γ : LCtx} (ls : List Level) (a nStep : Nat)
    (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
    (p : PackL E n k Dom Val Dom' Val' uSlot nStep ss (instLvlsCtx ls Γ)) :
    PackL E n k Dom Val Dom' Val' uSlot a (.linst ls a nStep hls hlen :: ss) Γ where
  fuel := .linst ls a nStep hls hlen p.fuel
  inv := .linst ls a nStep hls hlen p.inv
  run := .linst ls a nStep hls hlen p.run
  get := p.get
  slotTy := p.slotTy
  slotVal := p.slotVal

def packLEsub {n k j : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.assumption t))
    (hv : TyP E n
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t)))
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ)) :
    PackL E n k Dom Val Dom' Val' uSlot nIn
      (.esub j v t Γ
        (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
        hget
        (Skels.app (steps ss) (lift 0 j v))
        (Skels.app (steps ss) (lift 0 j t))
        hv :: ss) Γ where
  fuel := .esub j v t Γ
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.fuel
  inv := .esub j v t Γ
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.inv rfl rfl
  run := .esub rfl rfl p.run
  get := p.get
  slotTy := p.slotTy
  slotVal := p.slotVal

def packLLsub {n k j : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.letBinding t v))
    (hv : TyP E n
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t)))
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ)) :
    PackL E n k Dom Val Dom' Val' uSlot nIn
      (.lsub j v t Γ
        (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
        hget
        (Skels.app (steps ss) (lift 0 j v))
        (Skels.app (steps ss) (lift 0 j t))
        hv :: ss) Γ where
  fuel := .lsub j v t Γ
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.fuel
  inv := .lsub j v t Γ
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.inv rfl rfl
  run := .lsub rfl rfl p.run
  get := p.get
  slotTy := p.slotTy
  slotVal := p.slotVal

def packLCctx {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {A A' : Expr Nat} {u : Level}
    (hc : CvP E n
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      (.sort u))
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (.assumption A' :: Γ)) :
    PackL E n k Dom Val Dom' Val' uSlot nIn
      (.cctx 0 A'
        (Skels.app (steps ss) (lift 0 1 A'))
        (Skels.app (steps ss) (lift 0 1 A))
        u
        (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
        hc :: ss)
      (.assumption A :: Γ) where
  fuel := .cctx 0 A'
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      u
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      hc p.fuel
  inv := .cctx 0 A'
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      u
      (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      hc p.inv
  run := .cctx 0 A'
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      u A rfl rfl rfl rfl p.run
  get := p.get
  slotTy := p.slotTy
  slotVal := p.slotVal

def packLUnder {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx}
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ)
    (dLocal dFinal : LocalDecl)
    (hd : dFinal = Skels.onDecl (steps ss) dLocal) :
    PackL E n (k + 1) Dom Val Dom' Val' uSlot nIn (shiftAll dLocal dFinal ss) (dLocal :: Γ) where
  fuel := fuel_shiftAll dLocal dFinal ss nIn p.fuel
  inv := esInv_shiftAll dLocal dFinal ss p.inv
  run := runL_shift k Dom' Val' dLocal dFinal ss Γ hd p.run
  get := by
    rw [steps_shiftAll dLocal dFinal ss, get?_shift]
    exact p.get
  slotTy := by
    rw [steps_shiftAll dLocal dFinal ss, drop_shift]
    exact p.slotTy
  slotVal := by
    rw [steps_shiftAll dLocal dFinal ss, drop_shift]
    exact p.slotVal

def moveUnderL {n k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)} {Γ : LCtx}
    {dLocal dFinal : LocalDecl} {body T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (h : TyP E n
      (setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) body)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T)) :
    TyP E n (dFinal :: setLetB k Dom' Val' (Skels.ctx (steps ss) Γ))
      (Skels.app ((steps ss).map Skel.shift) body)
      (Skels.app ((steps ss).map Skel.shift) T) :=
  tyCastCtx (by
      rw [steps_shiftAll dLocal dFinal ss, ctx_shift, setLetB_succ, hd])
    (tyCast
      (congrArg (fun s => Skels.app s body) (steps_shiftAll dLocal dFinal ss))
      (congrArg (fun s => Skels.app s T) (steps_shiftAll dLocal dFinal ss))
      h)

def moveUnderCvL {n k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)} {Γ : LCtx}
    {dLocal dFinal : LocalDecl} {a b T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (h : CvP E n
      (setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) a)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) b)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T)) :
    CvP E n (dFinal :: setLetB k Dom' Val' (Skels.ctx (steps ss) Γ))
      (Skels.app ((steps ss).map Skel.shift) a)
      (Skels.app ((steps ss).map Skel.shift) b)
      (Skels.app ((steps ss).map Skel.shift) T) :=
  cvCastCtx (by
      rw [steps_shiftAll dLocal dFinal ss, ctx_shift, setLetB_succ, hd])
    (cvCast
      (congrArg (fun s => Skels.app s a) (steps_shiftAll dLocal dFinal ss))
      (congrArg (fun s => Skels.app s b) (steps_shiftAll dLocal dFinal ss))
      (congrArg (fun s => Skels.app s T) (steps_shiftAll dLocal dFinal ss))
      h)

/-! ## §5 slot-hit finishers and the variable walks -/

/-- A variable at the replaced let-slot, retyped at its old lookup. The new
    node types it at `lift 0 (k + 1) Dom'`; `conv` along the weakened `symm`
    sends that to `lift 0 (k + 1) Dom`. Twin of `retypeBvarSlot`. -/
def retypeLetBVarSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Val Dom' Val' : Expr Nat} {u : Level}
    (h : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u))
    (hget : Γ.get? k = some (.letBinding Dom Val)) :
    TyP E n (setLetB k Dom' Val' Γ) (.bvar k) (lift 0 (k + 1) Dom) := by
  let Γ' := setLetB k Dom' Val' Γ
  let pref := Γ'.take (k + 1)
  have hdrop : Γ'.drop (k + 1) = Γ.drop (k + 1) := drop_setLetB Dom' Val' Γ k
  have hlen : k < Γ.length := lt_length_of_get? Γ k hget
  have hlen' : k < Γ'.length := by rw [length_setLetB Dom' Val' Γ k]; exact hlen
  have hpref : pref.length = k + 1 := by
    rw [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hlen')]
  have hctx : pref ++ Γ.drop (k + 1) = Γ' := by
    rw [← hdrop]
    exact List.take_append_drop (k + 1) Γ'
  let hTy' := wkFront pref h.dr
  let hTy := tyCastCtx hctx (hpref ▸ hTy')
  have hlook : lookupType Γ' k = some (lift 0 (k + 1) Dom') :=
    lookupType_setLetB_hit Dom' Val' Γ k hget
  let hb := TyP.bvar E n Γ' k (lift 0 (k + 1) Dom') u hlook hTy
  let hsym := CvP.symm E n (Γ.drop (k + 1)) Dom Dom' (.sort u) h h.dr h.dl
  let hc0 := cvFront pref hsym
  let hc := cvCastCtx hctx (hpref ▸ hc0)
  exact TyP.conv E n Γ' (.bvar k) (lift 0 (k + 1) Dom') (lift 0 (k + 1) Dom) u hb hc

/-- A `zetaLocal` hit at the let-slot. The new node's right endpoint is the
    NEW value `lift 0 (k + 1) Val'`; `tyConv` on the lifted domain conversion
    retypes it at `lift 0 (k + 1) Dom`, and `trans` along the lifted `symm` of
    the value conversion sends it back to `lift 0 (k + 1) Val`. -/
def retypeLetBValSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Val Dom' Val' : Expr Nat} {u : Level}
    (hA : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u))
    (hv : CvP E n (Γ.drop (k + 1)) Val Val' Dom)
    (hget : Γ.get? k = some (.letBinding Dom Val)) :
    CvP E n (setLetB k Dom' Val' Γ)
      (.bvar k) (lift 0 (k + 1) Val) (lift 0 (k + 1) Dom) := by
  let Γ' := setLetB k Dom' Val' Γ
  let pref := Γ'.take (k + 1)
  have hdrop : Γ'.drop (k + 1) = Γ.drop (k + 1) := drop_setLetB Dom' Val' Γ k
  have hlen : k < Γ.length := lt_length_of_get? Γ k hget
  have hlen' : k < Γ'.length := by rw [length_setLetB Dom' Val' Γ k]; exact hlen
  have hpref : pref.length = k + 1 := by
    rw [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hlen')]
  have hctx : pref ++ Γ.drop (k + 1) = Γ' := by
    rw [← hdrop]
    exact List.take_append_drop (k + 1) Γ'
  have hlookV : lookupValue Γ' k = some (lift 0 (k + 1) Val') :=
    lookupValue_setLetB_hit Dom' Val' Γ k hget
  have hlookT : lookupType Γ' k = some (lift 0 (k + 1) Dom') :=
    lookupType_setLetB_hit Dom' Val' Γ k hget
  -- endpoint typings at the new decl's own slots
  let hTy' := wkFront pref hA.dr             -- TyP Γ' (lift Dom') (sort u)
  let hTy := tyCastCtx hctx (hpref ▸ hTy')
  let hb := TyP.bvar E n Γ' k (lift 0 (k + 1) Dom') u hlookT hTy
  let hv'0 := wkFront pref hv.dr             -- TyP Γ' (lift Val') (lift Dom)
  let hv'1 := tyCastCtx hctx (hpref ▸ hv'0)
  let hdom := cvFront pref hA                -- CvP Γ' (lift Dom)(lift Dom')(sort u)
  let hdomC := cvCastCtx hctx (hpref ▸ hdom)
  let hv' := TyP.conv E n Γ' (lift 0 (k + 1) Val') (lift 0 (k + 1) Dom)
    (lift 0 (k + 1) Dom') u hv'1 hdomC
  -- zetaLocal at the new slot: `bvar k ≡ lift Val'`, ascribed `lift Dom'`
  let hz := CvP.zetaLocal E n Γ' k (lift 0 (k + 1) Dom') (lift 0 (k + 1) Val')
    hlookV hlookT hv' hb hv'
  -- retype: `lift Dom' ≡ lift Dom`
  let hdomSymm := CvP.symm E n (Γ.drop (k + 1)) Dom Dom' (.sort u) hA hA.dr hA.dl
  let hdomSymm' := cvCastCtx hctx (hpref ▸ cvFront pref hdomSymm)
  let dl' := retypeLetBVarSlot (Val' := Val') hA hget  -- TyP Γ' (bvar k) (lift Dom)
  let hz' := CvP.tyConv E n Γ' (.bvar k) (lift 0 (k + 1) Val')
    (lift 0 (k + 1) Dom') (lift 0 (k + 1) Dom) u hz hdomSymm' dl' hv'1
  -- value patch: `lift Val' ≡ lift Val`, ascribed `lift Dom`
  let hvSymm := CvP.symm E n (Γ.drop (k + 1)) Val Val' Dom hv hv.dr hv.dl
  let hvSymm' := cvCastCtx hctx (hpref ▸ cvFront pref hvSymm)
  let hvl0 := wkFront pref hv.dl           -- TyP (pref ++ Γ.drop(k+1)) (lift Val)(lift Dom)
  let hvl := tyCastCtx hctx (hpref ▸ hvl0)
  exact CvP.trans E n Γ' (.bvar k) (lift 0 (k + 1) Val') (lift 0 (k + 1) Val)
    (lift 0 (k + 1) Dom) hz' hvSymm' dl' hvl

/-- Walk `.bvar i` through the skeleton. `k`, `Dom'`, `Val'` are the slot
    `setLetB` writes; they do not affect the renaming, only the final context.
    Twin of `bwalkAt`. -/
def bwalkAtL {n : Nat} (k : Nat) (Dom' Val' : Expr Nat) :
    (ss : List (PStep E n)) → (i : Nat) → (A : Expr Nat) → (Γ : LCtx) →
      lookupType Γ i = some A → EsInv ss → RunL k Dom' Val' ss Γ →
        BHit E n (Skels.ctx (steps ss) Γ)
          (setLetB k Dom' Val' (Skels.ctx (steps ss) Γ))
          (Skels.app (steps ss) (.bvar i)) (Skels.app (steps ss) A)
  | [], _, A, _, h, _, _ => .keep _ rfl h
  | .wk c d :: ss, i, A, Γ, h, .wk _ _ hinv, .wk _ _ hrun =>
      if hi : i < c then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (lift_bvar_lt hi))
          (bwalkAtL k Dom' Val' ss i (lift c 1 A) (insertAt d c Γ)
            (lookupType_insertAt_lt d hi h) hinv hrun)
      else
        BHit.castTerm
          (congrArg (Skels.app (steps ss)) (lift_bvar_ge (Nat.le_of_not_lt hi)))
          (bwalkAtL k Dom' Val' ss (i + 1) (lift c 1 A) (insertAt d c Γ)
            (lookupType_insertAt_ge d (Nat.le_of_not_lt hi) h) hinv hrun)
  | .esub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .esub _ _ _ _ _ _ _ _ _ hinv hr hT, .esub hΓ hctx hrun =>
      if hi : i < j then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))
          (bwalkAtL k Dom' Val' ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_lt hi h) hinv hrun)
      else if hj : j < i then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (bwalkAtL k Dom' Val' ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_gt hj h) hinv hrun)
      else by
        have hij : i = j := Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi)
        have hget' : Γ.get? i = some (.assumption t) := hij.symm ▸ (hΓ.symm ▸ hget)
        have hA : A = lift 0 (i + 1) t := lookupType_of_assumption hget' h
        subst hij
        have hinst : instantiate i (lift 0 i v) A = lift 0 i t := by
          rw [hA, instantiate_lift_cancel (i + 1) 0 i (lift 0 i v)
            (Nat.zero_le i) (Nat.lt_succ_self i) t, Nat.add_sub_cancel]
        have hterm : repl = Skels.app (Skel.esub i v :: steps ss) (.bvar i) := by
          rw [hr]
          simp only [Skels.app, Skel.app1, instantiate_bvar_eq]
        have hty : replT = Skels.app (Skel.esub i v :: steps ss) A := by
          rw [hT]
          simp only [Skels.app, Skel.app1, hinst]
        exact .repl (tyCastCtx hctx (tyCast hterm hty hv))
  | .lsub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .lsub _ _ _ _ _ _ _ _ _ hinv hr hT, .lsub hΓ hctx hrun =>
      if hi : i < j then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))
          (bwalkAtL k Dom' Val' ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_lt hi h) hinv hrun)
      else if hj : j < i then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (bwalkAtL k Dom' Val' ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_gt hj h) hinv hrun)
      else by
        have hij : i = j := Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi)
        have hget' : Γ.get? i = some (.letBinding t v) := hij.symm ▸ (hΓ.symm ▸ hget)
        have hA : A = lift 0 (i + 1) t := lookupType_of_letBinding hget' h
        subst hij
        have hinst : instantiate i (lift 0 i v) A = lift 0 i t := by
          rw [hA, instantiate_lift_cancel (i + 1) 0 i (lift 0 i v)
            (Nat.zero_le i) (Nat.lt_succ_self i) t, Nat.add_sub_cancel]
        have hterm : repl = Skels.app (Skel.esub i v :: steps ss) (.bvar i) := by
          rw [hr]
          simp only [Skels.app, Skel.app1, instantiate_bvar_eq]
        have hty : replT = Skels.app (Skel.esub i v :: steps ss) A := by
          rw [hT]
          simp only [Skels.app, Skel.app1, hinst]
        exact .repl (tyCastCtx hctx (tyCast hterm hty hv))
  | .linst ls a nStep hls hlen :: ss, i, A, Γ, h, .linst _ _ _ _ _ hinv,
      .linst _ _ _ _ _ hrun =>
      bwalkAtL k Dom' Val' ss i (instantiateLevels ls A) (instLvlsCtx ls Γ)
        (lookupType_instLvlsCtx_some ls h) hinv hrun
  | .cctx p Askel newTy oldTy u Γr hc :: ss, i, A, Γ, h,
      .cctx _ _ _ _ _ _ _ hinv, .cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun =>
      if hip : i = p then
        have hdec' : Γ.get? i = some (.assumption Aold) := hip ▸ hdec
        have hAold : A = lift 0 (i + 1) Aold := lookupType_of_assumption hdec' h
        let w := bwalkAtL k Dom' Val' ss p (lift 0 (p + 1) Askel) (setAssump p Askel Γ)
          (lookupType_setAssump_at Askel Γ p (hip ▸ h)) hinv hrun
        have hOld : oldTy = Skels.app (steps ss) A := by
          rw [hold, ← hip, hAold]
        let hc0 := cvCastCtx hctx (cvCast hnew hOld rfl hc)
        match w with
        | .keep j hterm hlook =>
            .retype j (Skels.app (steps ss) (lift 0 (p + 1) Askel))
              (hip.symm ▸ hterm) hlook (.cons u hc0 .nil)
        | .repl hv =>
            .repl (tyCast
              (by simp only [steps, List.map_cons, PStep.sk, Skels.app, Skel.app1, hip])
              rfl (TyP.conv E n _ _ _ _ u hv hc0))
        | .retype j B hterm hlook hc' =>
            .retype j B (hip.symm ▸ hterm) hlook (hc'.snoc u hc0)
      else
        bwalkAtL k Dom' Val' ss i A (setAssump p Askel Γ)
          (lookupType_setAssump_ne hip h) hinv hrun

/-- Finish a `bvar` after the walk: `keep`/`retype` at the let-slot are patched
    by `retypeLetBVarSlot`; every other index reads through `setLetB`. -/
def finishBvarL {n k : Nat} {Γpre : LCtx} {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level}
    {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u))
    (w : BHit E n Γpre (setLetB k Dom' Val' Γpre) term ty) :
    TyP E n (setLetB k Dom' Val' Γpre) term ty :=
  match w with
  | .repl hv => hv
  | .keep j hterm hlook =>
      if hj : j = k then
        tyCast ((congrArg Expr.bvar hj.symm).trans hterm.symm)
          (lookupType_of_letBinding hget (hj ▸ hlook)).symm
          (retypeLetBVarSlot hslot hget)
      else
        tyCast hterm.symm rfl
          (TyP.bvar E n _ j ty u (lookupType_setLetB_ne hj hlook) hA)
  | .retype j B hterm hlook hc =>
      if hj : j = k then
        ConvChain.apply
          (tyCast ((congrArg Expr.bvar hj.symm).trans hterm.symm)
            (lookupType_of_letBinding hget (hj ▸ hlook)).symm
            (retypeLetBVarSlot hslot hget))
          hc
      else
        let ⟨u', hB⟩ := chainSort hA hc
        ConvChain.apply
          (tyCast hterm.symm rfl
            (TyP.bvar E n _ j B u' (lookupType_setLetB_ne hj hlook) hB))
          hc

/-- Walk a let-bound variable's value through the skeleton. Identical to
    `valWalk`; the `i = k` (slot) case is not resolved here — `cvAtLet`'s
    `zetaLocal` arm emits `retypeLetBValSlot` for it. -/
def valWalkL {n : Nat} (k : Nat) (Dom' Val' : Expr Nat) :
    (ss : List (PStep E n)) → (i : Nat) → (v A : Expr Nat) → (Γ : LCtx) →
      lookupValue Γ i = some v → lookupType Γ i = some A →
      EsInv ss → RunL k Dom' Val' ss Γ →
        ValHit (Skels.ctx (steps ss) Γ)
          (Skels.app (steps ss) (.bvar i))
          (Skels.app (steps ss) v) (Skels.app (steps ss) A)
  | [], _, v, A, _, hv, ht, _, _ => .mk _ rfl hv ht
  | .wk c d :: ss, i, v, A, Γ, hv, ht, .wk _ _ hinv, .wk _ _ hrun =>
      if hi : i < c then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (lift_bvar_lt hi))
          (valWalkL k Dom' Val' ss i (lift c 1 v) (lift c 1 A) (insertAt d c Γ)
            (lookupValue_insertAt_lt d hi hv) (lookupType_insertAt_lt d hi ht) hinv hrun)
      else
        ValHit.castTerm
          (congrArg (Skels.app (steps ss)) (lift_bvar_ge (Nat.le_of_not_lt hi)))
          (valWalkL k Dom' Val' ss (i + 1) (lift c 1 v) (lift c 1 A) (insertAt d c Γ)
            (lookupValue_insertAt_ge d (Nat.le_of_not_lt hi) hv)
            (lookupType_insertAt_ge d (Nat.le_of_not_lt hi) ht) hinv hrun)
  | .esub j r t Γe Γr hget repl replT hv0 :: ss, i, v, A, Γ, hval, hty,
      .esub _ _ _ _ _ _ _ _ _ hinv _ _, .esub hΓ _ hrun =>
      if hi : i < j then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))
          (valWalkL k Dom' Val' ss i (instantiate j (lift 0 j r) v) (instantiate j (lift 0 j r) A)
            (substRemove r j Γ) (lookupValue_substRemove_lt hi hval)
            (lookupType_substRemove_lt hi hty) hinv hrun)
      else if hj : j < i then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (valWalkL k Dom' Val' ss (i - 1) (instantiate j (lift 0 j r) v)
            (instantiate j (lift 0 j r) A) (substRemove r j Γ)
            (lookupValue_substRemove_gt hj hval) (lookupType_substRemove_gt hj hty)
            hinv hrun)
      else by
        have hij : i = j := Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi)
        have hget' : Γ.get? j = some (.assumption t) := hΓ.symm ▸ hget
        cases (lookupValue_assumption_none hget').symm.trans (hij.symm ▸ hval)
  | .lsub j r t Γe Γr hget repl replT hv0 :: ss, i, v, A, Γ, hval, hty,
      .lsub _ _ _ _ _ _ _ _ _ hinv _ _, .lsub hΓ _ hrun =>
      if hi : i < j then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))
          (valWalkL k Dom' Val' ss i (instantiate j (lift 0 j r) v) (instantiate j (lift 0 j r) A)
            (substRemove r j Γ) (lookupValue_substRemove_lt hi hval)
            (lookupType_substRemove_lt hi hty) hinv hrun)
      else if hj : j < i then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (valWalkL k Dom' Val' ss (i - 1) (instantiate j (lift 0 j r) v)
            (instantiate j (lift 0 j r) A) (substRemove r j Γ)
            (lookupValue_substRemove_gt hj hval) (lookupType_substRemove_gt hj hty)
            hinv hrun)
      else by
        have hij : i = j := Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi)
        have hget' : Γ.get? j = some (.letBinding t r) := hΓ.symm ▸ hget
        have hvEq : v = lift 0 (j + 1) r := by
          have hlu : lookupValue Γ j = some (lift 0 (j + 1) r) := by
            unfold lookupValue
            rw [hget']
          exact Option.some.inj ((hij ▸ hval).symm.trans hlu)
        subst hij
        subst hvEq
        have hterm :
            Skels.app (steps (.lsub i r t Γe Γr hget repl replT hv0 :: ss)) (.bvar i) =
              Skels.app (steps (.lsub i r t Γe Γr hget repl replT hv0 :: ss))
                (lift 0 (i + 1) r) := by
          simp only [steps, List.map_cons, PStep.sk, Skels.app, Skel.app1,
            instantiate_bvar_eq]
          rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i r)
            (Nat.zero_le i) (Nat.lt_succ_self i) r, Nat.add_sub_cancel]
        exact .subst hterm
  | .linst ls a nStep hls hlen :: ss, i, v, A, Γ, hval, hty, .linst _ _ _ _ _ hinv,
      .linst _ _ _ _ _ hrun =>
      valWalkL k Dom' Val' ss i (instantiateLevels ls v) (instantiateLevels ls A) (instLvlsCtx ls Γ)
        (by rw [lookupValue_instLvlsCtx, hval, Option.map_some'])
        (lookupType_instLvlsCtx_some ls hty) hinv hrun
  | .cctx p Askel newTy oldTy u Γr hc :: ss, i, v, A, Γ, hval, hty,
      .cctx _ _ _ _ _ _ _ hinv, .cctx _ _ _ _ _ Aold hdec _ _ _ hrun =>
      if hip : i = p then by
        have hdec' : Γ.get? i = some (.assumption Aold) := hip ▸ hdec
        cases (lookupValue_assumption_none hdec').symm.trans hval
      else
        valWalkL k Dom' Val' ss i v A (setAssump p Askel Γ)
          (lookupValue_setAssump_ne hip hval) (lookupType_setAssump_ne hip hty) hinv hrun

/-! ## §6 the walk -/

mutual

/-- The let-slot walk on typings. Twin of `tyAt`: transports `D` through the
    skeleton in `p`, and rewrites the `.letBinding` slot `k` to
    `.letBinding Dom' Val'` along `p.slotTy`/`p.slotVal`. -/
def tyAtLet {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E)
    {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {e T : Expr Nat}
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ)
    (D : TyP Ei nIn Γ e T) :
    TyP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) Γ))
      (Skels.app (steps ss) e) (Skels.app (steps ss) T) :=
  match D with
  | .sort _ _ _ l k h => tySort l k h (steps ss)
  | .bvar _ _ _ i A _ hlu hA =>
      finishBvarL p.get p.slotTy (toSort (tyAtLet hW ι ιenv hext p hA))
        (bwalkAtL k Dom' Val' ss i A Γ hlu p.inv p.run)
  | .const _ _ _ r ls ls₀ m _ hres hlen hwf hls hT =>
      tyConst hW (hext r m hres) hlen hwf hls ss p.fuel
        (toSort (tyAtLet hW ι ιenv hext p hT))
  | .pi _ _ _ A u B v hA hB =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      tyPi A B u v (steps ss) (toSort (tyAtLet hW ι ιenv hext p hA))
        (toSort (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hB)))
  | .lam _ _ _ A u body B v hA hbody hB =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      tyLam A body B u v (steps ss) (toSort (tyAtLet hW ι ιenv hext p hA))
        (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hbody))
        (toSort (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hB)))
  | .app _ _ _ f a A B w hf ha hT =>
      tyApp f a A B w (steps ss) (toPi (tyAtLet hW ι ιenv hext p hf))
        (tyAtLet hW ι ιenv hext p ha) (toSort (tyAtLet hW ι ιenv hext p hT))
  | .letE _ _ _ A u value B body _ hA hv hb hT =>
      let dL : LocalDecl := .letBinding A value
      let dF := .letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value)
      let hd := (onDecl_let (steps ss) A value).symm
      tyLet A value B body u _ (steps ss) (toSort (tyAtLet hW ι ιenv hext p hA))
        (tyAtLet hW ι ιenv hext p hv)
        (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hb))
        (toSort (tyAtLet hW ι ιenv hext p hT))
  | .lit _ _ _ t _ hexp => tyLit t _ (steps ss) (tyAtLet hW ι ιenv hext p hexp)
  | .conv _ _ _ _ _ _ _ h hc =>
      TyP.conv E n _ _ _ _ (Skels.appLevel (steps ss) _)
        (tyAtLet hW ι ιenv hext p h) (cvToSort (cvAtLet hW ι ιenv hext p hc))
  | .wk _ _ Γ0 e0 A0 d c Di =>
      tyAtLet (Γ := Γ0) (nIn := nIn) (ss := .wk c d :: ss) (e := e0) (T := A0)
        hW ι ιenv hext (packLConsWk c d p) Di
  | .esub _ _ Γ0 e0 A0 t v j _ Di hget hv _ =>
      let hget' := (List.get?_eq_getElem? Γ0 j).symm ▸ hget
      let hv' := tyAtLet hW ι ιenv hext p hv
      tyAtLet (Γ := Γ0) (nIn := nIn)
        (ss := .esub j v t Γ0
          (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          hget'
          (Skels.app (steps ss) (lift 0 j v))
          (Skels.app (steps ss) (lift 0 j t))
          hv' :: ss)
        (e := e0) (T := A0)
        hW ι ιenv hext (packLEsub hget' hv' p) Di
  | .lsub _ _ Γ0 e0 A0 t v j _ Di hget hv _ =>
      let hget' := (List.get?_eq_getElem? Γ0 j).symm ▸ hget
      let hv' := tyAtLet hW ι ιenv hext p hv
      tyAtLet (Γ := Γ0) (nIn := nIn)
        (ss := .lsub j v t Γ0
          (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          hget'
          (Skels.app (steps ss) (lift 0 j v))
          (Skels.app (steps ss) (lift 0 j t))
          hv' :: ss)
        (e := e0) (T := A0)
        hW ι ιenv hext (packLLsub hget' hv' p) Di
  | .linst _ a _ Γ0 e0 A0 ls hls hlen Di =>
      tyAtLet (Γ := Γ0) (nIn := a) (ss := .linst ls a nIn hls hlen :: ss)
        (e := e0) (T := A0)
        hW ι ιenv hext (packLLinst ls a nIn hls hlen p) Di
  | .ewk E₀ _ _ _ _ _ hext' Di =>
      tyAtLet hW ι ιenv (envExt_trans hext' hext) p Di
  | .cctx _ _ Γ0 e0 T0 A A' _ Dinner hA =>
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
      tyAtLet (Γ := .assumption A :: Γ0) (nIn := nIn) (e := e0) (T := T0)
        hW ι ιenv hext (packLCctx flipped p) Dinner

/-- The let-slot walk on conversions. Twin of `cvAt`. The only new arm is
    `zetaLocal` at `j = k`, which is real under a `.letBinding` and emits
    `retypeLetBValSlot`. -/
def cvAtLet {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E)
    {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {a b T : Expr Nat}
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ)
    (C : CvP Ei nIn Γ a b T) :
    CvP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) Γ))
      (Skels.app (steps ss) a) (Skels.app (steps ss) b) (Skels.app (steps ss) T) :=
  match C with
  | .refl _ _ _ _ _ h dl dr =>
      CvP.refl E n _ _ _ (tyAtLet hW ι ιenv hext p h)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .symm _ _ _ _ _ _ h dl dr =>
      CvP.symm E n _ _ _ _ (cvAtLet hW ι ιenv hext p h)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .trans _ _ _ _ _ _ _ h1 h2 dl dr =>
      CvP.trans E n _ _ _ _ _ (cvAtLet hW ι ιenv hext p h1) (cvAtLet hW ι ιenv hext p h2)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .beta _ _ _ A body arg B u hA hbody harg dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvBeta (steps ss) A body arg B u
        (toSort (tyAtLet hW ι ιenv hext p hA))
        (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hbody))
        (tyAtLet hW ι ιenv hext p harg)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .zeta _ _ _ A value body B u hA hv hb dl dr =>
      let dL : LocalDecl := .letBinding A value
      let dF := .letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value)
      let hd := (onDecl_let (steps ss) A value).symm
      cvZeta (steps ss) A value body B u
        (toSort (tyAtLet hW ι ιenv hext p hA))
        (tyAtLet hW ι ιenv hext p hv)
        (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hb))
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .zetaLocal _ _ _ i vA val hval hty hv dl dr =>
      match valWalkL k Dom' Val' ss i val vA Γ hval hty p.inv p.run with
      | .subst hterm =>
          cvCast hterm.symm rfl rfl
            (CvP.refl E n _
              (Skels.app (steps ss) val) (Skels.app (steps ss) vA)
              (tyAtLet hW ι ιenv hext p hv)
              (tyCast hterm rfl (tyAtLet hW ι ιenv hext p dl))
              (tyAtLet hW ι ιenv hext p dr))
      | .mk j hterm hvl hlk =>
          if hj : j = k then by
            have hvl0 : lookupValue (Skels.ctx (steps ss) Γ) k =
                some (lift 0 (k + 1) Val) := by
              unfold lookupValue
              rw [p.get]
            have htk0 : lookupType (Skels.ctx (steps ss) Γ) k =
                some (lift 0 (k + 1) Dom) := by
              unfold lookupType
              rw [p.get]
            have hveq : Skels.app (steps ss) val = lift 0 (k + 1) Val :=
              Option.some.inj ((hj ▸ hvl).symm.trans hvl0)
            have hteq : Skels.app (steps ss) vA = lift 0 (k + 1) Dom :=
              Option.some.inj ((hj ▸ hlk).symm.trans htk0)
            exact cvCast ((congrArg Expr.bvar hj).symm.trans hterm.symm)
              hveq.symm hteq.symm
              (retypeLetBValSlot p.slotTy p.slotVal p.get)
          else
            cvCast hterm.symm rfl rfl
              (CvP.zetaLocal E n _ j _ _ (lookupValue_setLetB_ne hj hvl)
                (lookupType_setLetB_ne hj hlk)
                (tyAtLet hW ι ιenv hext p hv)
                (tyCast hterm rfl (tyAtLet hW ι ιenv hext p dl))
                (tyAtLet hW ι ιenv hext p dr))
  | .delta _ _ _ r ls m b hres hbody htr hlen hwf hb dl dr =>
      cvDelta hW ss nIn p.fuel (hext r m hres) hbody htr hlen hwf
        (tyAtLet hW ι ιenv hext p hb) (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .iota _ _ _ lhs rhs _ h hlhs hrhs dl dr =>
      CvP.iota E n _ _ _ _ (iotaUnder ι (steps ss) lhs rhs (ιenv hext h))
        (tyAtLet hW ι ιenv hext p hlhs) (tyAtLet hW ι ιenv hext p hrhs)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .lit _ _ _ t _ _ h hexp dl dr =>
      match h with
      | .of _ =>
          cvLit (steps ss) t _ (tyAtLet hW ι ιenv hext p hexp)
            (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .app _ _ _ f g a b A B h1 h2 dl dr =>
      cvApp (steps ss) f g a b A B
        (cvAtLet hW ι ιenv hext p h1) (cvAtLet hW ι ιenv hext p h2)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .lam _ _ _ A A' b b' B u hA hb dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvLam (steps ss) A A' b b' B u
        (cvToSort (cvAtLet hW ι ιenv hext p hA))
        (moveUnderCvL hd (cvAtLet hW ι ιenv hext (packLUnder p dL dF hd) hb))
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .pi _ _ _ A A' B B' u v hA hB dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvPi (steps ss) A A' B B' u v
        (cvToSort (cvAtLet hW ι ιenv hext p hA))
        (cvToSort (moveUnderCvL hd (cvAtLet hW ι ιenv hext (packLUnder p dL dF hd) hB)))
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .letE _ _ _ A A' v v' b b' B u hA hv hb dl dr =>
      let dL : LocalDecl := .letBinding A v
      let dF := .letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) v)
      let hd := (onDecl_let (steps ss) A v).symm
      cvLetE (steps ss) A A' v v' b b' B u
        (cvToSort (cvAtLet hW ι ιenv hext p hA))
        (cvAtLet hW ι ιenv hext p hv)
        (moveUnderCvL hd (cvAtLet hW ι ιenv hext (packLUnder p dL dF hd) hb))
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .sorts _ _ _ l₁ l₂ h dl dr =>
      cvSorts (steps ss) l₁ l₂ h (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .consts _ _ _ r ls ls' m hres hlen hwf hwf' h dl dr =>
      cvConsts hW ss nIn p.fuel (hext r m hres) hlen hwf hwf' h
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .eta _ _ _ f A B h dl dr =>
      cvEta (steps ss) f A B (tyAtLet hW ι ιenv hext p h)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .irr _ _ _ P pv q hP hp hq dl dr =>
      cvIrr (steps ss) P pv q (tyAtLet hW ι ιenv hext p hP)
        (tyAtLet hW ι ιenv hext p hp) (tyAtLet hW ι ιenv hext p hq)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .tyConv _ _ _ _ _ _ _ _ h hA dl dr =>
      CvP.tyConv E n _ _ _ _ _ _ (cvAtLet hW ι ιenv hext p h)
        (cvToSort (cvAtLet hW ι ιenv hext p hA))
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)
  | .wk _ _ Γ0 a0 b0 T0 d c h =>
      cvAtLet (Γ := Γ0) (nIn := nIn) (ss := .wk c d :: ss) (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packLConsWk c d p) h
  | .esub _ _ Γ0 a0 b0 T0 t v j _ h hget hv _ =>
      let hget' := (List.get?_eq_getElem? Γ0 j).symm ▸ hget
      let hv' := tyAtLet hW ι ιenv hext p hv
      cvAtLet (Γ := Γ0) (nIn := nIn)
        (ss := .esub j v t Γ0
          (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          hget'
          (Skels.app (steps ss) (lift 0 j v))
          (Skels.app (steps ss) (lift 0 j t))
          hv' :: ss)
        (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packLEsub hget' hv' p) h
  | .linst _ a _ Γ0 a0 b0 T0 ls hls hlen h =>
      cvAtLet (Γ := Γ0) (nIn := a) (ss := .linst ls a nIn hls hlen :: ss)
        (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packLLinst ls a nIn hls hlen p) h
  | .ewk E₀ _ _ _ _ _ _ hext' h =>
      cvAtLet hW ι ιenv (envExt_trans hext' hext) p h
  | .cctx _ _ Γ0 a0 b0 T0 A A' _ h hA =>
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
      cvAtLet (Γ := .assumption A :: Γ0) (nIn := nIn) (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packLCctx flipped p) h
  | .fsub _ _ _ A B S a b u hB hA hab dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvFsub (steps ss) A B S a b u
        (moveUnderL hd (tyAtLet hW ι ιenv hext (packLUnder p dL dF hd) hB))
        (toSort (tyAtLet hW ι ιenv hext p hA))
        (cvAtLet hW ι ιenv hext p hab)
        (tyAtLet hW ι ιenv hext p dl) (tyAtLet hW ι ιenv hext p dr)

end

/-! ## §7 entry point: `letCtxConvP` -/

/-- Empty let-slot pack. `FuelRel.nil` is this level bound, so `nIn = n`. -/
def packNilL {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {Γ : LCtx}
    (hget : Γ.get? k = some (.letBinding Dom Val))
    (hslotTy : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hslotVal : CvP E n (Γ.drop (k + 1)) Val Val' Dom) :
    PackL E n k Dom Val Dom' Val' uSlot n [] Γ where
  fuel := .nil
  inv := .nil
  run := .nil
  get := hget
  slotTy := hslotTy
  slotVal := hslotVal

/-- Replace the `.letBinding` at `k`, leaving the term and the ascribed type.
    The skeleton is empty, so this is `tyAtLet` at `FuelRel.nil`. -/
def tyCctxLetAt {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E) {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {e T : Expr Nat}
    (hget : Γ.get? k = some (.letBinding Dom Val))
    (hslotTy : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hslotVal : CvP E n (Γ.drop (k + 1)) Val Val' Dom)
    (D : TyP Ei n Γ e T) :
    TyP E n (setLetB k Dom' Val' Γ) e T :=
  tyAtLet (nIn := n) (ss := []) hW ι ιenv hext (packNilL hget hslotTy hslotVal) D

end Rcic.Syn

#print axioms Rcic.Syn.setLetB
#print axioms Rcic.Syn.setLetB_zero
#print axioms Rcic.Syn.setLetB_succ
#print axioms Rcic.Syn.setLetB_nil
#print axioms Rcic.Syn.length_setLetB
#print axioms Rcic.Syn.drop_setLetB
#print axioms Rcic.Syn.get?_setLetB_ne
#print axioms Rcic.Syn.lookupType_setLetB_ne
#print axioms Rcic.Syn.lookupValue_setLetB_ne
#print axioms Rcic.Syn.lookupType_setLetB_hit
#print axioms Rcic.Syn.lookupValue_setLetB_hit
#print axioms Rcic.Syn.lookupType_setLetB_at
#print axioms Rcic.Syn.setLetB_insertAt_gt
#print axioms Rcic.Syn.setLetB_insertAt_eq
#print axioms Rcic.Syn.shiftL_lsub_hctx
#print axioms Rcic.Syn.shiftL_esub_hctx
#print axioms Rcic.Syn.shiftL_cctx_hctx
#print axioms Rcic.Syn.runL_shift
#print axioms Rcic.Syn.packLWk
#print axioms Rcic.Syn.packLConsWk
#print axioms Rcic.Syn.packLLinst
#print axioms Rcic.Syn.packLEsub
#print axioms Rcic.Syn.packLLsub
#print axioms Rcic.Syn.packLCctx
#print axioms Rcic.Syn.packLUnder
#print axioms Rcic.Syn.moveUnderL
#print axioms Rcic.Syn.moveUnderCvL
#print axioms Rcic.Syn.retypeLetBVarSlot
#print axioms Rcic.Syn.retypeLetBValSlot
#print axioms Rcic.Syn.bwalkAtL
#print axioms Rcic.Syn.finishBvarL
#print axioms Rcic.Syn.valWalkL
#print axioms Rcic.Syn.tyAtLet
#print axioms Rcic.Syn.cvAtLet
#print axioms Rcic.Syn.packNilL
#print axioms Rcic.Syn.tyCctxLetAt