import rcic.RcicSynMember

/-!
# RcicSynWalk — typing and conversion under a transport skeleton (step 3q)

S3 §16. `tyAt` / `cvAt` walk a `TyP` / `CvP` through a head-innermost
skeleton. A transport is consed and the child is the recursive call. An
`esub` types its replacement against the outer steps only. A `cctx` walks
the stored domain conversion under one extra `wk` at cutoff 0, flips it,
and stores that. A `bvar` is `bwalkAt`; the slot is `retypeBvarSlot`.

`IotaPack` stays a premise. `DerivedIota` at the inner environment is
moved to the outer one by `ιenv`, separately from the pack.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## skeleton equations the walk needs -/

theorem onDecl_let :
    (ss : List Skel) → (A v : Expr Nat) →
      Skels.onDecl ss (.letBinding A v) =
        .letBinding (Skels.app ss A) (Skels.app ss v)
  | [], _, _ => rfl
  | .wk _ _ :: ss, A, v => by
      simp only [Skels.onDecl, Skel.onDecl, liftDecl, Skels.app, Skel.app1]
      exact onDecl_let ss _ _
  | .esub _ _ :: ss, A, v => by
      simp only [Skels.onDecl, Skel.onDecl, instDecl, Skels.app, Skel.app1]
      exact onDecl_let ss _ _
  | .linst _ :: ss, A, v => by
      simp only [Skels.onDecl, Skel.onDecl, instLvlsDecl, Skels.app, Skel.app1]
      exact onDecl_let ss _ _
  | .cctx _ _ :: ss, A, v => by
      simp only [Skels.onDecl, Skel.onDecl, Skels.app, Skel.app1]
      exact onDecl_let ss _ _

theorem appLevel_zero (ss : List Skel) : Skels.appLevel ss .zero = .zero := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk => simpa [Skels.appLevel] using ih
    | esub => simpa [Skels.appLevel] using ih
    | linst _ => simpa [Skels.appLevel, instLevel, lvlSubst] using ih
    | cctx => simpa [Skels.appLevel] using ih

/-- A binder shift sends every cutoff and every hole to at least 1, so
`.bvar 0` is fixed. -/
theorem app_shift_bvar0 (ss : List Skel) :
    Skels.app (ss.map Skel.shift) (.bvar 0) = .bvar 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk c _ =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [lift_bvar_lt (Nat.succ_pos c), ih]
    | esub j _ =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [instantiate_bvar_lt (Nat.succ_pos j), ih]
    | linst _ =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, instantiateLevels, ih]
    | cctx _ _ =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1, ih]

theorem app_eta_lam (ss : List Skel) (A f : Expr Nat) :
    Skels.app ss (.lam A (.app (lift 0 1 f) (.bvar 0))) =
      .lam (Skels.app ss A) (.app (lift 0 1 (Skels.app ss f)) (.bvar 0)) := by
  rw [app_lam, app_app, app_shift_bvar0, ← app_lift0]

theorem app_beta_lhs (ss : List Skel) (A body arg : Expr Nat) :
    Skels.app ss (.app (.lam A body) arg) =
      .app (.lam (Skels.app ss A) (Skels.app (ss.map Skel.shift) body))
        (Skels.app ss arg) := by
  rw [app_app, app_lam]

theorem lookupValue_setAssump_ne {k i : Nat} {v Dom' : Expr Nat} {Γ : LCtx}
    (hne : i ≠ k) (h : lookupValue Γ i = some v) :
    lookupValue (setAssump k Dom' Γ) i = some v := by
  unfold lookupValue at h ⊢
  rw [get?_setAssump_ne Dom' Γ k i hne]
  exact h

/-! ## pushing `Run` under one binder -/

variable {E : ResolvedEnv}

theorem shift_cctx_term {n : Nat} (dLocal dFinal : LocalDecl)
    {ss : List (PStep E n)} {p : Nat} {Askel newTy : Expr Nat}
    (hnew : newTy = Skels.app (steps ss) (lift 0 (p + 1) Askel)) :
    lift 0 1 newTy =
      Skels.app (steps (shiftAll (Skel.onDecl (.cctx p Askel) dLocal) dFinal ss))
        (lift 0 (p + 1 + 1) Askel) := by
  rw [hnew, steps_shiftAll, ← lift_lift_merge 1 (p + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) Askel,
    ← app_lift0]

theorem shift_lsub_hctx {n k j : Nat} {Dom' v : Expr Nat}
    {dLocal dFinal : LocalDecl} {Γ Γr Γe : LCtx} {t repl replT : Expr Nat}
    {hget : Γe.get? j = some (.letBinding t v)} {hv : TyP E n Γr repl replT}
    {ss : List (PStep E n)}
    (hd : dFinal =
      Skels.onDecl (steps (.lsub j v t Γe Γr hget repl replT hv :: ss)) dLocal)
    (hctx : Γr = setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ))) :
    insertAt dFinal 0 Γr =
      setAssump (k + 1) Dom'
        (Skels.ctx (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
          (substRemove v (j + 1) (dLocal :: Γ))) := by
  rw [hctx, insertAt_zero, substRemove_succ_cons, steps_shiftAll, ctx_shift, setAssump_succ]
  refine congrArg (fun d => d :: setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ))) ?_
  simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd

theorem shift_esub_hctx {n k j : Nat} {Dom' v : Expr Nat}
    {dLocal dFinal : LocalDecl} {Γ Γr Γe : LCtx} {t repl replT : Expr Nat}
    {hget : Γe.get? j = some (.assumption t)} {hv : TyP E n Γr repl replT}
    {ss : List (PStep E n)}
    (hd : dFinal =
      Skels.onDecl (steps (.esub j v t Γe Γr hget repl replT hv :: ss)) dLocal)
    (hctx : Γr = setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ))) :
    insertAt dFinal 0 Γr =
      setAssump (k + 1) Dom'
        (Skels.ctx (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
          (substRemove v (j + 1) (dLocal :: Γ))) := by
  rw [hctx, insertAt_zero, substRemove_succ_cons, steps_shiftAll, ctx_shift, setAssump_succ]
  refine congrArg (fun d => d :: setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ))) ?_
  simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd

theorem shift_cctx_hctx {n k p : Nat} {Dom' Askel newTy oldTy : Expr Nat} {u : Level}
    {dLocal dFinal : LocalDecl} {Γ Γr : LCtx} {hc : CvP E n Γr newTy oldTy (.sort u)}
    {ss : List (PStep E n)}
    (hd : dFinal =
      Skels.onDecl (steps (.cctx p Askel newTy oldTy u Γr hc :: ss)) dLocal)
    (hctx : Γr =
      setAssump k Dom' (Skels.ctx (steps ss) (setAssump p Askel Γ))) :
    insertAt dFinal 0 Γr =
      setAssump (k + 1) Dom'
        (Skels.ctx (steps (shiftAll (Skel.onDecl (.cctx p Askel) dLocal) dFinal ss))
          (setAssump (p + 1) Askel (dLocal :: Γ))) := by
  rw [hctx, insertAt_zero, setAssump_succ, steps_shiftAll, ctx_shift, setAssump_succ]
  refine congrArg
    (fun d => d :: setAssump k Dom' (Skels.ctx (steps ss) (setAssump p Askel Γ))) ?_
  simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd

def run_shift {n : Nat} (k : Nat) (Dom' : Expr Nat) (dLocal dFinal : LocalDecl) :
    (ss : List (PStep E n)) → (Γ : LCtx) →
      dFinal = Skels.onDecl (steps ss) dLocal →
      Run k Dom' ss Γ →
      Run (k + 1) Dom' (shiftAll dLocal dFinal ss) (dLocal :: Γ)
  | [], _, _, .nil => .nil
  | .wk c decl :: ss, Γ, hd, .wk _ _ h =>
      .wk (c + 1) decl
        (run_shift k Dom' (liftDecl c dLocal) dFinal ss (insertAt decl c Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .linst ls a nStep hls hlen :: ss, Γ, hd, .linst _ _ _ _ _ h =>
      .linst ls a nStep hls hlen
        (run_shift k Dom' (instLvlsDecl ls dLocal) dFinal ss (instLvlsCtx ls Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .esub j v t Γe Γr hget repl replT hv :: ss, Γ, hd, .esub hΓ hctx h =>
      .esub (congrArg (List.cons dLocal) hΓ) (shift_esub_hctx hd hctx)
        (run_shift k Dom' (instDecl j v dLocal) dFinal ss (substRemove v j Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .lsub j v t Γe Γr hget repl replT hv :: ss, Γ, hd, .lsub hΓ hctx h =>
      .lsub (congrArg (List.cons dLocal) hΓ) (shift_lsub_hctx hd hctx)
        (run_shift k Dom' (instDecl j v dLocal) dFinal ss (substRemove v j Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)
  | .cctx p Askel newTy oldTy u Γr hc :: ss, Γ, hd,
      .cctx _ _ _ _ _ Aold hdec hnew hold hctx h =>
      .cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u Aold
        (get?_cons_succ_assumption (d := dLocal) hdec)
        (shift_cctx_term dLocal dFinal hnew)
        (shift_cctx_term dLocal dFinal hold)
        (shift_cctx_hctx hd hctx)
        (run_shift k Dom' dLocal dFinal ss (setAssump p Askel Γ)
          (by simpa [steps, List.map_cons, PStep.sk, Skels.onDecl, Skel.onDecl] using hd) h)

/-! ## the pack: slot, fuel, and the two invariants, indexed so a cons refines -/

structure Pack (E : ResolvedEnv) (n k : Nat) (Dom Dom' : Expr Nat) (uSlot : Level)
    (nIn : Nat) (ss : List (PStep E n)) (Γ : LCtx) : Type where
  fuel : FuelRel ss nIn
  inv : EsInv ss
  run : Run k Dom' ss Γ
  get : (Skels.ctx (steps ss) Γ).get? k = some (.assumption Dom)
  slot : CvP E n ((Skels.ctx (steps ss) Γ).drop (k + 1)) Dom Dom' (.sort uSlot)

def packWk {n k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} (d : LocalDecl)
    (p : Pack E n k Dom Dom' uSlot nIn ss (insertAt d 0 Γ)) :
    Pack E n k Dom Dom' uSlot nIn (.wk 0 d :: ss) Γ where
  fuel := .wk 0 d p.fuel
  inv := .wk 0 d p.inv
  run := .wk 0 d p.run
  get := p.get
  slot := p.slot

def packLinst {n k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {Γ : LCtx} (ls : List Level) (a nStep : Nat)
    (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
    (p : Pack E n k Dom Dom' uSlot nStep ss (instLvlsCtx ls Γ)) :
    Pack E n k Dom Dom' uSlot a (.linst ls a nStep hls hlen :: ss) Γ where
  fuel := .linst ls a nStep hls hlen p.fuel
  inv := .linst ls a nStep hls hlen p.inv
  run := .linst ls a nStep hls hlen p.run
  get := p.get
  slot := p.slot

def packEsub {n k j : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.assumption t))
    (hv : TyP E n
      (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t)))
    (p : Pack E n k Dom Dom' uSlot nIn ss (substRemove v j Γ)) :
    Pack E n k Dom Dom' uSlot nIn
      (.esub j v t Γ
        (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
        hget
        (Skels.app (steps ss) (lift 0 j v))
        (Skels.app (steps ss) (lift 0 j t))
        hv :: ss) Γ where
  fuel := .esub j v t Γ
      (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.fuel
  inv := .esub j v t Γ
      (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.inv rfl rfl
  run := .esub rfl rfl p.run
  get := p.get
  slot := p.slot

def packLsub {n k j : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.letBinding t v))
    (hv : TyP E n
      (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t)))
    (p : Pack E n k Dom Dom' uSlot nIn ss (substRemove v j Γ)) :
    Pack E n k Dom Dom' uSlot nIn
      (.lsub j v t Γ
        (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
        hget
        (Skels.app (steps ss) (lift 0 j v))
        (Skels.app (steps ss) (lift 0 j t))
        hv :: ss) Γ where
  fuel := .lsub j v t Γ
      (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.fuel
  inv := .lsub j v t Γ
      (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      hget
      (Skels.app (steps ss) (lift 0 j v))
      (Skels.app (steps ss) (lift 0 j t))
      hv p.inv rfl rfl
  run := .lsub rfl rfl p.run
  get := p.get
  slot := p.slot

def packCctx {n k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {A A' : Expr Nat} {u : Level}
    (hc : CvP E n
      (setAssump k Dom' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      (.sort u))
    (p : Pack E n k Dom Dom' uSlot nIn ss (.assumption A' :: Γ)) :
    Pack E n k Dom Dom' uSlot nIn
      (.cctx 0 A'
        (Skels.app (steps ss) (lift 0 1 A'))
        (Skels.app (steps ss) (lift 0 1 A))
        u
        (setAssump k Dom' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
        hc :: ss)
      (.assumption A :: Γ) where
  fuel := .cctx 0 A'
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      u
      (setAssump k Dom' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      hc p.fuel
  inv := .cctx 0 A'
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      u
      (setAssump k Dom' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      hc p.inv
  run := .cctx 0 A'
      (Skels.app (steps ss) (lift 0 1 A'))
      (Skels.app (steps ss) (lift 0 1 A))
      u A rfl rfl rfl rfl p.run
  get := p.get
  slot := p.slot

def packUnder {n k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx}
    (p : Pack E n k Dom Dom' uSlot nIn ss Γ)
    (dLocal dFinal : LocalDecl)
    (hd : dFinal = Skels.onDecl (steps ss) dLocal) :
    Pack E n (k + 1) Dom Dom' uSlot nIn (shiftAll dLocal dFinal ss) (dLocal :: Γ) where
  fuel := fuel_shiftAll dLocal dFinal ss nIn p.fuel
  inv := esInv_shiftAll dLocal dFinal ss p.inv
  run := run_shift k Dom' dLocal dFinal ss Γ hd p.run
  get := by
    rw [steps_shiftAll dLocal dFinal ss, get?_shift]
    exact p.get
  slot := by
    rw [steps_shiftAll dLocal dFinal ss, drop_shift]
    exact p.slot

def moveUnder {n k : Nat} {Dom' : Expr Nat} {ss : List (PStep E n)} {Γ : LCtx}
    {dLocal dFinal : LocalDecl} {body T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (h : TyP E n
      (setAssump (k + 1) Dom'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) body)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T)) :
    TyP E n (dFinal :: setAssump k Dom' (Skels.ctx (steps ss) Γ))
      (Skels.app ((steps ss).map Skel.shift) body)
      (Skels.app ((steps ss).map Skel.shift) T) :=
  tyCastCtx (by
      rw [steps_shiftAll dLocal dFinal ss, ctx_shift, setAssump_succ, hd])
    (tyCast
      (congrArg (fun s => Skels.app s body) (steps_shiftAll dLocal dFinal ss))
      (congrArg (fun s => Skels.app s T) (steps_shiftAll dLocal dFinal ss))
      h)

def moveUnderCv {n k : Nat} {Dom' : Expr Nat} {ss : List (PStep E n)} {Γ : LCtx}
    {dLocal dFinal : LocalDecl} {a b T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (h : CvP E n
      (setAssump (k + 1) Dom'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) a)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) b)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T)) :
    CvP E n (dFinal :: setAssump k Dom' (Skels.ctx (steps ss) Γ))
      (Skels.app ((steps ss).map Skel.shift) a)
      (Skels.app ((steps ss).map Skel.shift) b)
      (Skels.app ((steps ss).map Skel.shift) T) :=
  cvCastCtx (by
      rw [steps_shiftAll dLocal dFinal ss, ctx_shift, setAssump_succ, hd])
    (cvCast
      (congrArg (fun s => Skels.app s a) (steps_shiftAll dLocal dFinal ss))
      (congrArg (fun s => Skels.app s b) (steps_shiftAll dLocal dFinal ss))
      (congrArg (fun s => Skels.app s T) (steps_shiftAll dLocal dFinal ss))
      h)

def toSort {n : Nat} {Γ : LCtx} {e : Expr Nat} {ss : List Skel} {u : Level}
    (h : TyP E n Γ e (Skels.app ss (.sort u))) :
    TyP E n Γ e (.sort (Skels.appLevel ss u)) :=
  tyCast rfl (app_sort ss u) h

def toSortZero {n : Nat} {Γ : LCtx} {e : Expr Nat} {ss : List Skel}
    (h : TyP E n Γ e (Skels.app ss (.sort .zero))) :
    TyP E n Γ e (.sort .zero) :=
  tyCast rfl ((app_sort ss .zero).trans (congrArg Expr.sort (appLevel_zero ss))) h

def toPi {n : Nat} {Γ : LCtx} {f : Expr Nat} {ss : List Skel} {A B : Expr Nat}
    (h : TyP E n Γ f (Skels.app ss (.pi A B))) :
    TyP E n Γ f (.pi (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)) :=
  tyCast rfl (app_pi ss A B) h

def cvToSort {n : Nat} {Γ : LCtx} {a b : Expr Nat} {ss : List Skel} {u : Level}
    (h : CvP E n Γ a b (Skels.app ss (.sort u))) :
    CvP E n Γ a b (.sort (Skels.appLevel ss u)) :=
  cvCast rfl rfl (app_sort ss u) h

def cvToPi {n : Nat} {Γ : LCtx} {f g : Expr Nat} {ss : List Skel} {A B : Expr Nat}
    (h : CvP E n Γ f g (Skels.app ss (.pi A B))) :
    CvP E n Γ f g (.pi (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)) :=
  cvCast rfl rfl (app_pi ss A B) h

/-! ## what a renamed variable has become, on the known pre-context -/

inductive BHit (E : ResolvedEnv) (n : Nat) (pre fin : LCtx) (term ty : Expr Nat) : Type where
  | keep (j : Nat) (hterm : term = .bvar j) (hlook : lookupType pre j = some ty)
  | repl (hv : TyP E n fin term ty)
  | retype (j : Nat) (B : Expr Nat) (hterm : term = .bvar j)
      (hlook : lookupType pre j = some B) (hc : ConvChain E n fin B ty)

def BHit.castTerm {n : Nat} {pre fin : LCtx} {term ty term' : Expr Nat}
    (h : term' = term) (w : BHit E n pre fin term ty) : BHit E n pre fin term' ty :=
  match w with
  | .keep j ht hl => .keep j (h.trans ht) hl
  | .repl hv => .repl (tyCast h.symm rfl hv)
  | .retype j B ht hl hc => .retype j B (h.trans ht) hl hc

def bwalkAt {n : Nat} (k : Nat) (Dom' : Expr Nat) :
    (ss : List (PStep E n)) → (i : Nat) → (A : Expr Nat) → (Γ : LCtx) →
      lookupType Γ i = some A → EsInv ss → Run k Dom' ss Γ →
        BHit E n (Skels.ctx (steps ss) Γ)
          (setAssump k Dom' (Skels.ctx (steps ss) Γ))
          (Skels.app (steps ss) (.bvar i)) (Skels.app (steps ss) A)
  | [], _, A, _, h, _, _ => .keep _ rfl h
  | .wk c d :: ss, i, A, Γ, h, .wk _ _ hinv, .wk _ _ hrun =>
      if hi : i < c then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (lift_bvar_lt hi))
          (bwalkAt k Dom' ss i (lift c 1 A) (insertAt d c Γ)
            (lookupType_insertAt_lt d hi h) hinv hrun)
      else
        BHit.castTerm
          (congrArg (Skels.app (steps ss)) (lift_bvar_ge (Nat.le_of_not_lt hi)))
          (bwalkAt k Dom' ss (i + 1) (lift c 1 A) (insertAt d c Γ)
            (lookupType_insertAt_ge d (Nat.le_of_not_lt hi) h) hinv hrun)
  | .esub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .esub _ _ _ _ _ _ _ _ _ hinv hr hT, .esub hΓ hctx hrun =>
      if hi : i < j then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))
          (bwalkAt k Dom' ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_lt hi h) hinv hrun)
      else if hj : j < i then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (bwalkAt k Dom' ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
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
          (bwalkAt k Dom' ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_lt hi h) hinv hrun)
      else if hj : j < i then
        BHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (bwalkAt k Dom' ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
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
      bwalkAt k Dom' ss i (instantiateLevels ls A) (instLvlsCtx ls Γ)
        (lookupType_instLvlsCtx_some ls h) hinv hrun
  | .cctx p Askel newTy oldTy u Γr hc :: ss, i, A, Γ, h,
      .cctx _ _ _ _ _ _ _ hinv, .cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun =>
      if hip : i = p then
        have hdec' : Γ.get? i = some (.assumption Aold) := hip ▸ hdec
        have hAold : A = lift 0 (i + 1) Aold := lookupType_of_assumption hdec' h
        let w := bwalkAt k Dom' ss p (lift 0 (p + 1) Askel) (setAssump p Askel Γ)
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
        bwalkAt k Dom' ss i A (setAssump p Askel Γ)
          (lookupType_setAssump_ne hip h) hinv hrun

def chainSort {n : Nat} {Γ : LCtx} {B ty : Expr Nat} {u0 : Level}
    (hA : TyP E n Γ ty (.sort u0)) (hc : ConvChain E n Γ B ty) :
    Σ u : Level, TyP E n Γ B (.sort u) :=
  match hc with
  | .nil => ⟨u0, hA⟩
  | .cons u h _ => ⟨u, h.dl⟩

def finishBvar {n k : Nat} {Γpre : LCtx} {Dom Dom' : Expr Nat} {uSlot u : Level}
    {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.assumption Dom))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setAssump k Dom' Γpre) ty (.sort u))
    (w : BHit E n Γpre (setAssump k Dom' Γpre) term ty) :
    TyP E n (setAssump k Dom' Γpre) term ty :=
  match w with
  | .repl hv => hv
  | .keep j hterm hlook =>
      if hj : j = k then
        tyCast ((congrArg Expr.bvar hj.symm).trans hterm.symm)
          (lookupType_of_assumption hget (hj ▸ hlook)).symm
          (retypeBvarSlot hslot hget)
      else
        tyCast hterm.symm rfl
          (TyP.bvar E n _ j ty u (lookupType_setAssump_ne hj hlook) hA)
  | .retype j B hterm hlook hc =>
      if hj : j = k then
        ConvChain.apply
          (tyCast ((congrArg Expr.bvar hj.symm).trans hterm.symm)
            (lookupType_of_assumption hget (hj ▸ hlook)).symm
            (retypeBvarSlot hslot hget))
          hc
      else
        let ⟨u', hB⟩ := chainSort hA hc
        ConvChain.apply
          (tyCast hterm.symm rfl
            (TyP.bvar E n _ j B u' (lookupType_setAssump_ne hj hlook) hB))
          hc

/-! ## a let-bound variable, for `zetaLocal` -/

inductive ValHit (pre : LCtx) (term v A : Expr Nat) : Type where
  | mk (j : Nat) (hterm : term = .bvar j)
      (hval : lookupValue pre j = some v) (hty : lookupType pre j = some A)
  | subst (hterm : term = v)

def ValHit.castTerm {pre : LCtx} {term term' v A : Expr Nat}
    (h : term' = term) (w : ValHit pre term v A) : ValHit pre term' v A :=
  match w with
  | .mk j ht hv hl => .mk j (h.trans ht) hv hl
  | .subst ht => .subst (h.trans ht)

def valWalk {n : Nat} (k : Nat) (Dom' : Expr Nat) :
    (ss : List (PStep E n)) → (i : Nat) → (v A : Expr Nat) → (Γ : LCtx) →
      lookupValue Γ i = some v → lookupType Γ i = some A →
      EsInv ss → Run k Dom' ss Γ →
        ValHit (Skels.ctx (steps ss) Γ)
          (Skels.app (steps ss) (.bvar i))
          (Skels.app (steps ss) v) (Skels.app (steps ss) A)
  | [], _, v, A, _, hv, ht, _, _ => .mk _ rfl hv ht
  | .wk c d :: ss, i, v, A, Γ, hv, ht, .wk _ _ hinv, .wk _ _ hrun =>
      if hi : i < c then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (lift_bvar_lt hi))
          (valWalk k Dom' ss i (lift c 1 v) (lift c 1 A) (insertAt d c Γ)
            (lookupValue_insertAt_lt d hi hv) (lookupType_insertAt_lt d hi ht) hinv hrun)
      else
        ValHit.castTerm
          (congrArg (Skels.app (steps ss)) (lift_bvar_ge (Nat.le_of_not_lt hi)))
          (valWalk k Dom' ss (i + 1) (lift c 1 v) (lift c 1 A) (insertAt d c Γ)
            (lookupValue_insertAt_ge d (Nat.le_of_not_lt hi) hv)
            (lookupType_insertAt_ge d (Nat.le_of_not_lt hi) ht) hinv hrun)
  | .esub j r t Γe Γr hget repl replT hv0 :: ss, i, v, A, Γ, hval, hty,
      .esub _ _ _ _ _ _ _ _ _ hinv _ _, .esub hΓ _ hrun =>
      if hi : i < j then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))
          (valWalk k Dom' ss i (instantiate j (lift 0 j r) v) (instantiate j (lift 0 j r) A)
            (substRemove r j Γ) (lookupValue_substRemove_lt hi hval)
            (lookupType_substRemove_lt hi hty) hinv hrun)
      else if hj : j < i then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (valWalk k Dom' ss (i - 1) (instantiate j (lift 0 j r) v)
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
          (valWalk k Dom' ss i (instantiate j (lift 0 j r) v) (instantiate j (lift 0 j r) A)
            (substRemove r j Γ) (lookupValue_substRemove_lt hi hval)
            (lookupType_substRemove_lt hi hty) hinv hrun)
      else if hj : j < i then
        ValHit.castTerm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))
          (valWalk k Dom' ss (i - 1) (instantiate j (lift 0 j r) v)
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
      valWalk k Dom' ss i (instantiateLevels ls v) (instantiateLevels ls A) (instLvlsCtx ls Γ)
        (by rw [lookupValue_instLvlsCtx, hval, Option.map_some'])
        (lookupType_instLvlsCtx_some ls hty) hinv hrun
  | .cctx p Askel newTy oldTy u Γr hc :: ss, i, v, A, Γ, hval, hty,
      .cctx _ _ _ _ _ _ _ hinv, .cctx _ _ _ _ _ Aold hdec _ _ _ hrun =>
      if hip : i = p then by
        have hdec' : Γ.get? i = some (.assumption Aold) := hip ▸ hdec
        cases (lookupValue_assumption_none hdec').symm.trans hval
      else
        valWalk k Dom' ss i v A (setAssump p Askel Γ)
          (lookupValue_setAssump_ne hip hval) (lookupType_setAssump_ne hip hty) hinv hrun

def packConsWk {n k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} (c : Nat) (d : LocalDecl)
    (p : Pack E n k Dom Dom' uSlot nIn ss (insertAt d c Γ)) :
    Pack E n k Dom Dom' uSlot nIn (.wk c d :: ss) Γ where
  fuel := .wk c d p.fuel
  inv := .wk c d p.inv
  run := .wk c d p.run
  get := p.get
  slot := p.slot

theorem app_sort_succ (ss : List Skel) (l : Level) :
    Skels.app ss (.sort (.succ l)) = .sort (.succ (Skels.appLevel ss l)) := by
  rw [app_sort, appLevel_succ]

theorem app_sort_imax (ss : List Skel) (u v : Level) :
    Skels.app ss (.sort (.imax u v)) =
      .sort (.imax (Skels.appLevel ss u) (Skels.appLevel (ss.map Skel.shift) v)) := by
  rw [app_sort, appLevel_imax]
  exact congrArg (fun l => Expr.sort (Level.imax (Skels.appLevel ss u) l))
    (appLevel_shift ss v).symm

/-! ## rule nodes, from children already in the final context -/

variable {n : Nat} {Γ : LCtx}

def cvBeta (ss : List Skel) (A body arg B : Expr Nat) (u : Level)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hbody : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B))
    (harg : TyP E n Γ (Skels.app ss arg) (Skels.app ss A))
    (dl : TyP E n Γ (Skels.app ss (.app (.lam A body) arg))
      (Skels.app ss (instantiate0 arg B)))
    (dr : TyP E n Γ (Skels.app ss (instantiate0 arg body))
      (Skels.app ss (instantiate0 arg B))) :
    CvP E n Γ (Skels.app ss (.app (.lam A body) arg))
      (Skels.app ss (instantiate0 arg body)) (Skels.app ss (instantiate0 arg B)) :=
  cvCast (app_beta_lhs ss A body arg).symm (app_inst0 ss arg body).symm
    (app_inst0 ss arg B).symm
    (CvP.beta E n Γ (Skels.app ss A) (Skels.app (ss.map Skel.shift) body)
      (Skels.app ss arg) (Skels.app (ss.map Skel.shift) B) (Skels.appLevel ss u)
      hA hbody harg
      (tyCast (app_beta_lhs ss A body arg) (app_inst0 ss arg B) dl)
      (tyCast (app_inst0 ss arg body) (app_inst0 ss arg B) dr))

def cvZeta (ss : List Skel) (A value body B : Expr Nat) (u : Level)
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hv : TyP E n Γ (Skels.app ss value) (Skels.app ss A))
    (hb : TyP E n (.letBinding (Skels.app ss A) (Skels.app ss value) :: Γ)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B))
    (dl : TyP E n Γ (Skels.app ss (.letE A value body))
      (Skels.app ss (instantiate0 value B)))
    (dr : TyP E n Γ (Skels.app ss (instantiate0 value body))
      (Skels.app ss (instantiate0 value B))) :
    CvP E n Γ (Skels.app ss (.letE A value body))
      (Skels.app ss (instantiate0 value body)) (Skels.app ss (instantiate0 value B)) :=
  cvCast (app_letE ss A value body).symm (app_inst0 ss value body).symm
    (app_inst0 ss value B).symm
    (CvP.zeta E n Γ (Skels.app ss A) (Skels.app ss value)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B)
      (Skels.appLevel ss u) hA hv hb
      (tyCast (app_letE ss A value body) (app_inst0 ss value B) dl)
      (tyCast (app_inst0 ss value body) (app_inst0 ss value B) dr))

def cvDelta (hW : CvWalkHyp E) (ss : List (PStep E n)) (nIn : Nat) (hfuel : FuelRel ss nIn)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true)
    (hb : TyP E n Γ (Skels.app (steps ss) (instantiateLevels ls b))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype)))
    (dl : TyP E n Γ (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype)))
    (dr : TyP E n Γ (Skels.app (steps ss) (instantiateLevels ls b))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))) :
    CvP E n Γ (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (instantiateLevels ls b))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype)) :=
  cvCast (app_const (steps ss) r ls).symm
    (app_instantiateLevels_body hW hres hbody (steps ss) ls hlen).symm
    (app_instantiateLevels_member hW hres (steps ss) ls hlen).symm
    (CvP.delta E n Γ r (Skels.appLevels (steps ss) ls) m b hres hbody htr
      (length_appLevels_of hlen) (levelsBounded_steps ss nIn hfuel ls hwf)
      (tyCast (app_instantiateLevels_body hW hres hbody (steps ss) ls hlen)
        (app_instantiateLevels_member hW hres (steps ss) ls hlen) hb)
      (tyCast (app_const (steps ss) r ls)
        (app_instantiateLevels_member hW hres (steps ss) ls hlen) dl)
      (tyCast (app_instantiateLevels_body hW hres hbody (steps ss) ls hlen)
        (app_instantiateLevels_member hW hres (steps ss) ls hlen) dr))

def cvApp (ss : List Skel) (f g a b A B : Expr Nat)
    (h1 : CvP E n Γ (Skels.app ss f) (Skels.app ss g) (Skels.app ss (.pi A B)))
    (h2 : CvP E n Γ (Skels.app ss a) (Skels.app ss b) (Skels.app ss A))
    (dl : TyP E n Γ (Skels.app ss (.app f a)) (Skels.app ss (instantiate0 a B)))
    (dr : TyP E n Γ (Skels.app ss (.app g b)) (Skels.app ss (instantiate0 a B))) :
    CvP E n Γ (Skels.app ss (.app f a)) (Skels.app ss (.app g b))
      (Skels.app ss (instantiate0 a B)) :=
  cvCast (app_app ss f a).symm (app_app ss g b).symm (app_inst0 ss a B).symm
    (CvP.app E n Γ (Skels.app ss f) (Skels.app ss g) (Skels.app ss a) (Skels.app ss b)
      (Skels.app ss A) (Skels.app (ss.map Skel.shift) B) (cvToPi h1) h2
      (tyCast (app_app ss f a) (app_inst0 ss a B) dl)
      (tyCast (app_app ss g b) (app_inst0 ss a B) dr))

def cvLam (ss : List Skel) (A A' b b' B : Expr Nat) (u : Level)
    (hA : CvP E n Γ (Skels.app ss A) (Skels.app ss A') (.sort (Skels.appLevel ss u)))
    (hb : CvP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) b) (Skels.app (ss.map Skel.shift) b')
      (Skels.app (ss.map Skel.shift) B))
    (dl : TyP E n Γ (Skels.app ss (.lam A b)) (Skels.app ss (.pi A B)))
    (dr : TyP E n Γ (Skels.app ss (.lam A' b')) (Skels.app ss (.pi A B))) :
    CvP E n Γ (Skels.app ss (.lam A b)) (Skels.app ss (.lam A' b'))
      (Skels.app ss (.pi A B)) :=
  cvCast (app_lam ss A b).symm (app_lam ss A' b').symm (app_pi ss A B).symm
    (CvP.lam E n Γ (Skels.app ss A) (Skels.app ss A')
      (Skels.app (ss.map Skel.shift) b) (Skels.app (ss.map Skel.shift) b')
      (Skels.app (ss.map Skel.shift) B) (Skels.appLevel ss u) hA hb
      (tyCast (app_lam ss A b) (app_pi ss A B) dl)
      (tyCast (app_lam ss A' b') (app_pi ss A B) dr))

def cvPi (ss : List Skel) (A A' B B' : Expr Nat) (u v : Level)
    (hA : CvP E n Γ (Skels.app ss A) (Skels.app ss A') (.sort (Skels.appLevel ss u)))
    (hB : CvP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) B) (Skels.app (ss.map Skel.shift) B')
      (.sort (Skels.appLevel (ss.map Skel.shift) v)))
    (dl : TyP E n Γ (Skels.app ss (.pi A B)) (Skels.app ss (.sort (.imax u v))))
    (dr : TyP E n Γ (Skels.app ss (.pi A' B')) (Skels.app ss (.sort (.imax u v)))) :
    CvP E n Γ (Skels.app ss (.pi A B)) (Skels.app ss (.pi A' B'))
      (Skels.app ss (.sort (.imax u v))) :=
  cvCast (app_pi ss A B).symm (app_pi ss A' B').symm (app_sort_imax ss u v).symm
    (CvP.pi E n Γ (Skels.app ss A) (Skels.app ss A')
      (Skels.app (ss.map Skel.shift) B) (Skels.app (ss.map Skel.shift) B')
      (Skels.appLevel ss u) (Skels.appLevel (ss.map Skel.shift) v) hA hB
      (tyCast (app_pi ss A B) (app_sort_imax ss u v) dl)
      (tyCast (app_pi ss A' B') (app_sort_imax ss u v) dr))

def cvLetE (ss : List Skel) (A A' v v' b b' B : Expr Nat) (u : Level)
    (hA : CvP E n Γ (Skels.app ss A) (Skels.app ss A') (.sort (Skels.appLevel ss u)))
    (hv : CvP E n Γ (Skels.app ss v) (Skels.app ss v') (Skels.app ss A))
    (hb : CvP E n (.letBinding (Skels.app ss A) (Skels.app ss v) :: Γ)
      (Skels.app (ss.map Skel.shift) b) (Skels.app (ss.map Skel.shift) b')
      (Skels.app (ss.map Skel.shift) B))
    (dl : TyP E n Γ (Skels.app ss (.letE A v b)) (Skels.app ss (instantiate0 v B)))
    (dr : TyP E n Γ (Skels.app ss (.letE A' v' b')) (Skels.app ss (instantiate0 v B))) :
    CvP E n Γ (Skels.app ss (.letE A v b)) (Skels.app ss (.letE A' v' b'))
      (Skels.app ss (instantiate0 v B)) :=
  cvCast (app_letE ss A v b).symm (app_letE ss A' v' b').symm (app_inst0 ss v B).symm
    (CvP.letE E n Γ (Skels.app ss A) (Skels.app ss A') (Skels.app ss v) (Skels.app ss v')
      (Skels.app (ss.map Skel.shift) b) (Skels.app (ss.map Skel.shift) b')
      (Skels.app (ss.map Skel.shift) B) (Skels.appLevel ss u) hA hv hb
      (tyCast (app_letE ss A v b) (app_inst0 ss v B) dl)
      (tyCast (app_letE ss A' v' b') (app_inst0 ss v B) dr))

def cvSorts (ss : List Skel) (l₁ l₂ : Level) (h : eqN l₁ l₂)
    (dl : TyP E n Γ (Skels.app ss (.sort l₁)) (Skels.app ss (.sort (.succ l₁))))
    (dr : TyP E n Γ (Skels.app ss (.sort l₂)) (Skels.app ss (.sort (.succ l₁)))) :
    CvP E n Γ (Skels.app ss (.sort l₁)) (Skels.app ss (.sort l₂))
      (Skels.app ss (.sort (.succ l₁))) :=
  cvCast (app_sort ss l₁).symm (app_sort ss l₂).symm (app_sort_succ ss l₁).symm
    (CvP.sorts E n Γ (Skels.appLevel ss l₁) (Skels.appLevel ss l₂) (eqN_appLevel ss h)
      (tyCast (app_sort ss l₁) (app_sort_succ ss l₁) dl)
      (tyCast (app_sort ss l₂) (app_sort_succ ss l₁) dr))

def cvConsts (hW : CvWalkHyp E) (ss : List (PStep E n)) (nIn : Nat) (hfuel : FuelRel ss nIn)
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true) (hwf' : levelsBounded nIn ls' = true)
    (h : eqNList ls ls')
    (dl : TyP E n Γ (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype)))
    (dr : TyP E n Γ (Skels.app (steps ss) (.const r ls'))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))) :
    CvP E n Γ (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (.const r ls'))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype)) :=
  cvCast (app_const (steps ss) r ls).symm (app_const (steps ss) r ls').symm
    (app_instantiateLevels_member hW hres (steps ss) ls hlen).symm
    (CvP.consts E n Γ r (Skels.appLevels (steps ss) ls) (Skels.appLevels (steps ss) ls') m
      hres (length_appLevels_of hlen)
      (levelsBounded_steps ss nIn hfuel ls hwf)
      (levelsBounded_steps ss nIn hfuel ls' hwf')
      (eqNList_appLevels (steps ss) h)
      (tyCast (app_const (steps ss) r ls)
        (app_instantiateLevels_member hW hres (steps ss) ls hlen) dl)
      (tyCast (app_const (steps ss) r ls')
        (app_instantiateLevels_member hW hres (steps ss) ls hlen) dr))

def cvEta (ss : List Skel) (f A B : Expr Nat)
    (h : TyP E n Γ (Skels.app ss f) (Skels.app ss (.pi A B)))
    (dl : TyP E n Γ (Skels.app ss (.lam A (.app (lift 0 1 f) (.bvar 0))))
      (Skels.app ss (.pi A B)))
    (dr : TyP E n Γ (Skels.app ss f) (Skels.app ss (.pi A B))) :
    CvP E n Γ (Skels.app ss (.lam A (.app (lift 0 1 f) (.bvar 0))))
      (Skels.app ss f) (Skels.app ss (.pi A B)) :=
  cvCast (app_eta_lam ss A f).symm rfl (app_pi ss A B).symm
    (CvP.eta E n Γ (Skels.app ss f) (Skels.app ss A)
      (Skels.app (ss.map Skel.shift) B) (toPi h)
      (tyCast (app_eta_lam ss A f) (app_pi ss A B) dl)
      (tyCast rfl (app_pi ss A B) dr))

def cvIrr (ss : List Skel) (P p q : Expr Nat)
    (hP : TyP E n Γ (Skels.app ss P) (Skels.app ss (.sort .zero)))
    (hp : TyP E n Γ (Skels.app ss p) (Skels.app ss P))
    (hq : TyP E n Γ (Skels.app ss q) (Skels.app ss P))
    (dl : TyP E n Γ (Skels.app ss p) (Skels.app ss P))
    (dr : TyP E n Γ (Skels.app ss q) (Skels.app ss P)) :
    CvP E n Γ (Skels.app ss p) (Skels.app ss q) (Skels.app ss P) :=
  CvP.irr E n Γ (Skels.app ss P) (Skels.app ss p) (Skels.app ss q)
    (toSortZero hP) hp hq dl dr

def cvLit (ss : List Skel) (t : Nat) (T : Expr Nat)
    (hexp : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T))
    (dl : TyP E n Γ (Skels.app ss (.lit t)) (Skels.app ss T))
    (dr : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T)) :
    CvP E n Γ (Skels.app ss (.lit t)) (Skels.app ss (natExpand t)) (Skels.app ss T) :=
  cvCast (app_lit ss t).symm (app_natExpand ss t).symm rfl
    (CvP.lit E n Γ t (natExpand t) (Skels.app ss T) (.of t)
      (tyCast (app_natExpand ss t) rfl hexp)
      (tyCast (app_lit ss t) rfl dl)
      (tyCast (app_natExpand ss t) rfl dr))

def cvFsub (ss : List Skel) (A B S a b : Expr Nat) (u : Level)
    (hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) B) (Skels.app (ss.map Skel.shift) S))
    (hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u)))
    (hab : CvP E n Γ (Skels.app ss a) (Skels.app ss b) (Skels.app ss A))
    (dl : TyP E n Γ (Skels.app ss (instantiate0 a B)) (Skels.app ss (instantiate0 a S)))
    (dr : TyP E n Γ (Skels.app ss (instantiate0 b B)) (Skels.app ss (instantiate0 a S))) :
    CvP E n Γ (Skels.app ss (instantiate0 a B)) (Skels.app ss (instantiate0 b B))
      (Skels.app ss (instantiate0 a S)) :=
  cvCast (app_inst0 ss a B).symm (app_inst0 ss b B).symm (app_inst0 ss a S).symm
    (CvP.fsub E n Γ (Skels.app ss A) (Skels.app (ss.map Skel.shift) B)
      (Skels.app (ss.map Skel.shift) S) (Skels.app ss a) (Skels.app ss b)
      (Skels.appLevel ss u) hB hA hab
      (tyCast (app_inst0 ss a B) (app_inst0 ss a S) dl)
      (tyCast (app_inst0 ss b B) (app_inst0 ss a S) dr))

/-! ## the walk -/

mutual

def tyAt {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E)
    {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {e T : Expr Nat}
    (p : Pack E n k Dom Dom' uSlot nIn ss Γ)
    (D : TyP Ei nIn Γ e T) :
    TyP E n (setAssump k Dom' (Skels.ctx (steps ss) Γ))
      (Skels.app (steps ss) e) (Skels.app (steps ss) T) :=
  match D with
  | .sort _ _ _ l k h => tySort l k h (steps ss)
  | .bvar _ _ _ i A _ hlu hA =>
      finishBvar p.get p.slot (toSort (tyAt hW ι ιenv hext p hA))
        (bwalkAt k Dom' ss i A Γ hlu p.inv p.run)
  | .const _ _ _ r ls ls₀ m _ hres hlen hwf hls hT =>
      tyConst hW (hext r m hres) hlen hwf hls ss p.fuel
        (toSort (tyAt hW ι ιenv hext p hT))
  | .pi _ _ _ A u B v hA hB =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      tyPi A B u v (steps ss) (toSort (tyAt hW ι ιenv hext p hA))
        (toSort (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hB)))
  | .lam _ _ _ A u body B v hA hbody hB =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      tyLam A body B u v (steps ss) (toSort (tyAt hW ι ιenv hext p hA))
        (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hbody))
        (toSort (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hB)))
  | .app _ _ _ f a A B w hf ha hT =>
      tyApp f a A B w (steps ss) (toPi (tyAt hW ι ιenv hext p hf))
        (tyAt hW ι ιenv hext p ha) (toSort (tyAt hW ι ιenv hext p hT))
  | .letE _ _ _ A u value B body _ hA hv hb hT =>
      let dL : LocalDecl := .letBinding A value
      let dF := .letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value)
      let hd := (onDecl_let (steps ss) A value).symm
      tyLet A value B body u _ (steps ss) (toSort (tyAt hW ι ιenv hext p hA))
        (tyAt hW ι ιenv hext p hv)
        (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hb))
        (toSort (tyAt hW ι ιenv hext p hT))
  | .lit _ _ _ t _ hexp => tyLit t _ (steps ss) (tyAt hW ι ιenv hext p hexp)
  | .conv _ _ _ _ _ _ _ h hc =>
      TyP.conv E n _ _ _ _ (Skels.appLevel (steps ss) _)
        (tyAt hW ι ιenv hext p h) (cvToSort (cvAt hW ι ιenv hext p hc))
  | .wk _ _ Γ0 e0 A0 d c Di =>
      tyAt (Γ := Γ0) (nIn := nIn) (ss := .wk c d :: ss) (e := e0) (T := A0)
        hW ι ιenv hext (packConsWk c d p) Di
  | .esub _ _ Γ0 e0 A0 t v j _ Di hget hv _ =>
      let hget' := (List.get?_eq_getElem? Γ0 j).symm ▸ hget
      let hv' := tyAt hW ι ιenv hext p hv
      tyAt (Γ := Γ0) (nIn := nIn)
        (ss := .esub j v t Γ0
          (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          hget'
          (Skels.app (steps ss) (lift 0 j v))
          (Skels.app (steps ss) (lift 0 j t))
          hv' :: ss)
        (e := e0) (T := A0)
        hW ι ιenv hext (packEsub hget' hv' p) Di
  | .lsub _ _ Γ0 e0 A0 t v j _ Di hget hv _ =>
      let hget' := (List.get?_eq_getElem? Γ0 j).symm ▸ hget
      let hv' := tyAt hW ι ιenv hext p hv
      tyAt (Γ := Γ0) (nIn := nIn)
        (ss := .lsub j v t Γ0
          (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          hget'
          (Skels.app (steps ss) (lift 0 j v))
          (Skels.app (steps ss) (lift 0 j t))
          hv' :: ss)
        (e := e0) (T := A0)
        hW ι ιenv hext (packLsub hget' hv' p) Di
  | .linst _ a _ Γ0 e0 A0 ls hls hlen Di =>
      tyAt (Γ := Γ0) (nIn := a) (ss := .linst ls a nIn hls hlen :: ss) (e := e0) (T := A0)
        hW ι ιenv hext (packLinst ls a nIn hls hlen p) Di
  | .ewk E₀ _ _ _ _ _ hext' Di =>
      tyAt hW ι ιenv (envExt_trans hext' hext) p Di
  | .cctx _ _ Γ0 e0 T0 A A' _ Dinner hA =>
      let pA := packWk (.assumption A') p
      let hc0 := cvAt hW ι ιenv hext pA hA
      let hc1 := cvToSort hc0
      let hOld := toSort hc0.dl
      let hNew := toSort hc0.dr
      let flipped :=
        CvP.symm E n
          (setAssump k Dom' (Skels.ctx (steps ss) (.assumption A' :: Γ0)))
          (Skels.app (steps ss) (lift 0 1 A))
          (Skels.app (steps ss) (lift 0 1 A'))
          (.sort (Skels.appLevel (steps ss) _))
          hc1 hNew hOld
      tyAt (Γ := .assumption A :: Γ0) (nIn := nIn) (e := e0) (T := T0)
        hW ι ιenv hext (packCctx flipped p) Dinner

def cvAt {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E)
    {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {a b T : Expr Nat}
    (p : Pack E n k Dom Dom' uSlot nIn ss Γ)
    (C : CvP Ei nIn Γ a b T) :
    CvP E n (setAssump k Dom' (Skels.ctx (steps ss) Γ))
      (Skels.app (steps ss) a) (Skels.app (steps ss) b) (Skels.app (steps ss) T) :=
  match C with
  | .refl _ _ _ _ _ h dl dr =>
      CvP.refl E n _ _ _ (tyAt hW ι ιenv hext p h)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .symm _ _ _ _ _ _ h dl dr =>
      CvP.symm E n _ _ _ _ (cvAt hW ι ιenv hext p h)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .trans _ _ _ _ _ _ _ h1 h2 dl dr =>
      CvP.trans E n _ _ _ _ _ (cvAt hW ι ιenv hext p h1) (cvAt hW ι ιenv hext p h2)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .beta _ _ _ A body arg B u hA hbody harg dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvBeta (steps ss) A body arg B u
        (toSort (tyAt hW ι ιenv hext p hA))
        (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hbody))
        (tyAt hW ι ιenv hext p harg)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .zeta _ _ _ A value body B u hA hv hb dl dr =>
      let dL : LocalDecl := .letBinding A value
      let dF := .letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value)
      let hd := (onDecl_let (steps ss) A value).symm
      cvZeta (steps ss) A value body B u
        (toSort (tyAt hW ι ιenv hext p hA))
        (tyAt hW ι ιenv hext p hv)
        (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hb))
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .zetaLocal _ _ _ i vA val hval hty hv dl dr =>
      match valWalk k Dom' ss i val vA Γ hval hty p.inv p.run with
      | .subst hterm =>
          cvCast hterm.symm rfl rfl
            (CvP.refl E n _
              (Skels.app (steps ss) val) (Skels.app (steps ss) vA)
              (tyAt hW ι ιenv hext p hv)
              (tyCast hterm rfl (tyAt hW ι ιenv hext p dl))
              (tyAt hW ι ιenv hext p dr))
      | .mk j hterm hvl hlk =>
          if hj : j = k then by
            cases (lookupValue_assumption_none (hj.symm ▸ p.get)).symm.trans hvl
          else
            cvCast hterm.symm rfl rfl
              (CvP.zetaLocal E n _ j _ _ (lookupValue_setAssump_ne hj hvl)
                (lookupType_setAssump_ne hj hlk)
                (tyAt hW ι ιenv hext p hv)
                (tyCast hterm rfl (tyAt hW ι ιenv hext p dl))
                (tyAt hW ι ιenv hext p dr))
  | .delta _ _ _ r ls m b hres hbody htr hlen hwf hb dl dr =>
      cvDelta hW ss nIn p.fuel (hext r m hres) hbody htr hlen hwf
        (tyAt hW ι ιenv hext p hb) (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .iota _ _ _ lhs rhs _ h hlhs hrhs dl dr =>
      CvP.iota E n _ _ _ _ (iotaUnder ι (steps ss) lhs rhs (ιenv hext h))
        (tyAt hW ι ιenv hext p hlhs) (tyAt hW ι ιenv hext p hrhs)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .lit _ _ _ t _ _ h hexp dl dr =>
      match h with
      | .of _ =>
          cvLit (steps ss) t _ (tyAt hW ι ιenv hext p hexp)
            (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .app _ _ _ f g a b A B h1 h2 dl dr =>
      cvApp (steps ss) f g a b A B
        (cvAt hW ι ιenv hext p h1) (cvAt hW ι ιenv hext p h2)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .lam _ _ _ A A' b b' B u hA hb dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvLam (steps ss) A A' b b' B u
        (cvToSort (cvAt hW ι ιenv hext p hA))
        (moveUnderCv hd (cvAt hW ι ιenv hext (packUnder p dL dF hd) hb))
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .pi _ _ _ A A' B B' u v hA hB dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvPi (steps ss) A A' B B' u v
        (cvToSort (cvAt hW ι ιenv hext p hA))
        (cvToSort (moveUnderCv hd (cvAt hW ι ιenv hext (packUnder p dL dF hd) hB)))
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .letE _ _ _ A A' v v' b b' B u hA hv hb dl dr =>
      let dL : LocalDecl := .letBinding A v
      let dF := .letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) v)
      let hd := (onDecl_let (steps ss) A v).symm
      cvLetE (steps ss) A A' v v' b b' B u
        (cvToSort (cvAt hW ι ιenv hext p hA))
        (cvAt hW ι ιenv hext p hv)
        (moveUnderCv hd (cvAt hW ι ιenv hext (packUnder p dL dF hd) hb))
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .sorts _ _ _ l₁ l₂ h dl dr =>
      cvSorts (steps ss) l₁ l₂ h (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .consts _ _ _ r ls ls' m hres hlen hwf hwf' h dl dr =>
      cvConsts hW ss nIn p.fuel (hext r m hres) hlen hwf hwf' h
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .eta _ _ _ f A B h dl dr =>
      cvEta (steps ss) f A B (tyAt hW ι ιenv hext p h)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .irr _ _ _ P pv q hP hp hq dl dr =>
      cvIrr (steps ss) P pv q (tyAt hW ι ιenv hext p hP)
        (tyAt hW ι ιenv hext p hp) (tyAt hW ι ιenv hext p hq)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .tyConv _ _ _ _ _ _ _ _ h hA dl dr =>
      CvP.tyConv E n _ _ _ _ _ _ (cvAt hW ι ιenv hext p h)
        (cvToSort (cvAt hW ι ιenv hext p hA))
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)
  | .wk _ _ Γ0 a0 b0 T0 d c h =>
      cvAt (Γ := Γ0) (nIn := nIn) (ss := .wk c d :: ss) (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packConsWk c d p) h
  | .esub _ _ Γ0 a0 b0 T0 t v j _ h hget hv _ =>
      let hget' := (List.get?_eq_getElem? Γ0 j).symm ▸ hget
      let hv' := tyAt hW ι ιenv hext p hv
      cvAt (Γ := Γ0) (nIn := nIn)
        (ss := .esub j v t Γ0
          (setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ0)))
          hget'
          (Skels.app (steps ss) (lift 0 j v))
          (Skels.app (steps ss) (lift 0 j t))
          hv' :: ss)
        (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packEsub hget' hv' p) h
  | .linst _ a _ Γ0 a0 b0 T0 ls hls hlen h =>
      cvAt (Γ := Γ0) (nIn := a) (ss := .linst ls a nIn hls hlen :: ss)
        (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packLinst ls a nIn hls hlen p) h
  | .ewk E₀ _ _ _ _ _ _ hext' h =>
      cvAt hW ι ιenv (envExt_trans hext' hext) p h
  | .cctx _ _ Γ0 a0 b0 T0 A A' _ h hA =>
      let pA := packWk (.assumption A') p
      let hc0 := cvAt hW ι ιenv hext pA hA
      let hc1 := cvToSort hc0
      let hOld := toSort hc0.dl
      let hNew := toSort hc0.dr
      let flipped :=
        CvP.symm E n
          (setAssump k Dom' (Skels.ctx (steps ss) (.assumption A' :: Γ0)))
          (Skels.app (steps ss) (lift 0 1 A))
          (Skels.app (steps ss) (lift 0 1 A'))
          (.sort (Skels.appLevel (steps ss) _))
          hc1 hNew hOld
      cvAt (Γ := .assumption A :: Γ0) (nIn := nIn) (a := a0) (b := b0) (T := T0)
        hW ι ιenv hext (packCctx flipped p) h
  | .fsub _ _ _ A B S a b u hB hA hab dl dr =>
      let dL : LocalDecl := .assumption A
      let dF := .assumption (Skels.app (steps ss) A)
      let hd := (onDecl_assumption (steps ss) A).symm
      cvFsub (steps ss) A B S a b u
        (moveUnder hd (tyAt hW ι ιenv hext (packUnder p dL dF hd) hB))
        (toSort (tyAt hW ι ιenv hext p hA))
        (cvAt hW ι ιenv hext p hab)
        (tyAt hW ι ιenv hext p dl) (tyAt hW ι ιenv hext p dr)

end

end Rcic.Syn
