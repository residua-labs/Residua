import rcic.RcicSynCctx

/-!
# RcicSynTyAt — the variable walk under a transport skeleton (step 3m)

S3 §14. This file is the stored step and `bwalk`. `tyAt` is not defined
here yet. When it is, `tyCctxAt` is `tyAt` of the empty skeleton. A
transport conses a step and recurses on the child. At an `esub` node the
replacement is typed against the outer steps only and stored; the hole
returns that typing and does not walk the inner derivation again. A
`bvar` whose renamed index is the slot is `retypeBvarSlot`. Two `cctx`
hits on one variable need not share a sort, so `bwalk` returns a
`ConvChain` and the consumer applies `TyP.conv` once per link.

`IotaPack` is the open ι obligation (S3 §13): a nonempty `wk` or `esub`
skeleton rebuilds `CvP.iota` only when `DerivedIota` transports. A
`cctx`-only skeleton does not need it.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv}

/-- `DerivedIota` along every transport the skeleton applies. `IotaLift`
and `IotaSubst` are `Type`s on main (`RcicDeclarative.lean`). There is no
`IotaLinst` there, so level instantiation is a premise of the pack. -/
structure IotaPack (E : ResolvedEnv) : Type 1 where
  liftι : IotaLift E
  substι : IotaSubst E
  linstι : ∀ (ls : List Level) (lhs rhs : Expr Nat),
    DerivedIota E lhs rhs → DerivedIota E (instantiateLevels ls lhs) (instantiateLevels ls rhs)

/-- Walk a skeleton over a derived ι equation. -/
def iotaUnder (ι : IotaPack E) :
    (ss : List Skel) → (lhs rhs : Expr Nat) → DerivedIota E lhs rhs →
      DerivedIota E (Skels.app ss lhs) (Skels.app ss rhs)
  | [], _, _, h => h
  | .wk c _ :: ss, lhs, rhs, h =>
      iotaUnder ι ss (lift c 1 lhs) (lift c 1 rhs) (ι.liftι lhs rhs h c)
  | .esub j v :: ss, lhs, rhs, h =>
      iotaUnder ι ss
        (instantiate j (lift 0 j v) lhs) (instantiate j (lift 0 j v) rhs)
        (ι.substι lhs rhs h (lift 0 j v) j)
  | .linst ls :: ss, lhs, rhs, h =>
      iotaUnder ι ss (instantiateLevels ls lhs) (instantiateLevels ls rhs)
        (ι.linstι ls lhs rhs h)
  | .cctx _ _ :: ss, lhs, rhs, h => iotaUnder ι ss lhs rhs h

/-! ## levels through the skeleton -/

theorem appLevel_succ (ss : List Skel) (l : Level) :
    Skels.appLevel ss (.succ l) = .succ (Skels.appLevel ss l) := by
  induction ss generalizing l with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk => simpa [Skels.appLevel] using ih l
    | esub => simpa [Skels.appLevel] using ih l
    | linst ls => simpa [Skels.appLevel, instLevel_succ] using ih (instLevel ls l)
    | cctx => simpa [Skels.appLevel] using ih l

theorem appLevel_imax (ss : List Skel) (u v : Level) :
    Skels.appLevel ss (.imax u v) = .imax (Skels.appLevel ss u) (Skels.appLevel ss v) := by
  induction ss generalizing u v with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk => simpa [Skels.appLevel] using ih u v
    | esub => simpa [Skels.appLevel] using ih u v
    | linst ls =>
        simpa [Skels.appLevel, instLevel_imax] using ih (instLevel ls u) (instLevel ls v)
    | cctx => simpa [Skels.appLevel] using ih u v

theorem eqN_appLevel (ss : List Skel) {l l' : Level} (h : eqN l l') :
    eqN (Skels.appLevel ss l) (Skels.appLevel ss l') := by
  induction ss generalizing l l' with
  | nil => exact h
  | cons s ss ih =>
    cases s with
    | wk => simpa [Skels.appLevel] using ih h
    | esub => simpa [Skels.appLevel] using ih h
    | linst ls => simpa [Skels.appLevel] using ih (eqN_instLevel h ls)
    | cctx => simpa [Skels.appLevel] using ih h

theorem eqNList_appLevels (ss : List Skel) {ls ls' : List Level} (h : eqNList ls ls') :
    eqNList (Skels.appLevels ss ls) (Skels.appLevels ss ls') := by
  induction ss generalizing ls ls' with
  | nil => exact h
  | cons s ss ih =>
    cases s with
    | wk => simpa [Skels.appLevels] using ih h
    | esub => simpa [Skels.appLevels] using ih h
    | linst lv => simpa [Skels.appLevels] using ih (eqNList_map_instLevel lv _ _ h)
    | cctx => simpa [Skels.appLevels] using ih h

/-! ## `lift 0 1` through a skeleton -/

theorem app_lift0 (ss : List Skel) (e : Expr Nat) :
    lift 0 1 (Skels.app ss e) = Skels.app (ss.map Skel.shift) (lift 0 1 e) := by
  induction ss generalizing e with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk c _ =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [ih (lift c 1 e), lift_lift_permute 1 1 c 0 (Nat.zero_le c) e, Nat.add_comm 1 c]
    | esub j v =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [ih (instantiate j (lift 0 j v) e),
        lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) e,
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v, Nat.add_comm 1 j]
    | linst ls =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [ih (instantiateLevels ls e), lift_instantiateLevels ls 1 e 0]
    | cctx _ _ =>
      simp only [List.map_cons, Skels.app, Skel.shift, Skel.app1]
      rw [ih e]

/-- A level-closed term is fixed by `wk` and `esub`. `linst` is
`instantiateLevels_compose`. The const arm of `tyAt` needs this: the
skeleton of a member type is only a level substitution. -/
theorem app_instantiateLevels_closed (ss : List Skel) (ls : List Level) (e : Expr Nat)
    (hcl : ∀ c, lift c 1 e = e) (hbnd : exprLevelsBounded ls.length e = true) :
    Skels.app ss (instantiateLevels ls e) =
      instantiateLevels (Skels.appLevels ss ls) e := by
  induction ss generalizing ls with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk c _ =>
      simp only [Skels.app, Skel.app1, Skels.appLevels]
      rw [lift_instantiateLevels ls 1 e c, hcl c]
      exact ih ls hbnd
    | esub j v =>
      simp only [Skels.app, Skel.app1, Skels.appLevels]
      rw [instantiate_closed_gen (instantiateLevels ls e) 0
        (instantiateLevels_closed hcl ls 0) j (Nat.zero_le j) (lift 0 j v)]
      exact ih ls hbnd
    | linst ls0 =>
      simp only [Skels.app, Skel.app1, Skels.appLevels]
      have hbnd' : exprLevelsBounded (ls.map (instLevel ls0)).length e = true := by
        rw [List.length_map]
        exact hbnd
      rw [instantiateLevels_compose ls0 ls e hbnd]
      exact ih (ls.map (instLevel ls0)) hbnd'
    | cctx _ _ =>
      simp only [Skels.app, Skel.app1, Skels.appLevels]
      exact ih ls hbnd

/-! ## the stored step, its skeleton, and the two invariants -/

/-- One transport. `esub` stores the replacement, already typed in the final
context, and the assumption it wrote over. `cctx` stores the conversion from
the new lookup to the old ascribed type, already in the final context. -/
inductive PStep (E : ResolvedEnv) (n : Nat) : Type where
  | wk (c : Nat) (d : LocalDecl)
  | esub (j : Nat) (v t : Expr Nat) (Γe Γr : LCtx)
      (hget : Γe.get? j = some (.assumption t))
      (repl replT : Expr Nat) (hv : TyP E n Γr repl replT)
  | lsub (j : Nat) (v t : Expr Nat) (Γe Γr : LCtx)
      (hget : Γe.get? j = some (.letBinding t v))
      (repl replT : Expr Nat) (hv : TyP E n Γr repl replT)
  | linst (ls : List Level) (a nStep : Nat)
      (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
  | cctx (p : Nat) (Askel newTy oldTy : Expr Nat) (u : Level) (Γr : LCtx)
      (hc : CvP E n Γr newTy oldTy (.sort u))

/-- `esub` keeps the hole and the replacement; `cctx` keeps the index and the new type. -/
def PStep.sk {n : Nat} : PStep E n → Skel
  | .wk c d => .wk c d
  | .esub j v _ _ _ _ _ _ _ => .esub j v
  | .lsub j v _ _ _ _ _ _ _ => .esub j v
  | .linst ls _ _ _ _ => .linst ls
  | .cctx p Askel _ _ _ _ _ => .cctx p Askel

def steps {n : Nat} (ss : List (PStep E n)) : List Skel := ss.map PStep.sk

/-- Fuel: the head is innermost. A `linst` step's child fuel is `a` and
its conclusion fuel is the tail's start fuel. -/
inductive FuelRel {E : ResolvedEnv} {n : Nat} : List (PStep E n) → Nat → Prop where
  | nil : FuelRel [] n
  | wk (c d) (h : FuelRel ss nIn) : FuelRel (.wk c d :: ss) nIn
  | esub (j v t Γe Γr hget repl replT hv) (h : FuelRel ss nIn) :
      FuelRel (.esub j v t Γe Γr hget repl replT hv :: ss) nIn
  | lsub (j v t Γe Γr hget repl replT hv) (h : FuelRel ss nIn) :
      FuelRel (.lsub j v t Γe Γr hget repl replT hv :: ss) nIn
  | cctx (p Askel newTy oldTy u Γr hc) (h : FuelRel ss nIn) :
      FuelRel (.cctx p Askel newTy oldTy u Γr hc :: ss) nIn
  | linst (ls a nStep hls hlen) (h : FuelRel ss nStep) :
      FuelRel (.linst ls a nStep hls hlen :: ss) a

theorem levelsBounded_steps {n : Nat} :
    (ss : List (PStep E n)) → (nIn : Nat) → FuelRel ss nIn →
      (ls : List Level) → levelsBounded nIn ls = true →
        levelsBounded n (Skels.appLevels (steps ss) ls) = true
  | [], _, .nil, _, hwf => hwf
  | .wk _ _ :: ss, nIn, .wk _ _ h, ls, hwf => by
      simp only [steps, List.map_cons, PStep.sk, Skels.appLevels]
      exact levelsBounded_steps ss nIn h ls hwf
  | .esub _ _ _ _ _ _ _ _ _ :: ss, nIn, .esub _ _ _ _ _ _ _ _ _ h, ls, hwf => by
      simp only [steps, List.map_cons, PStep.sk, Skels.appLevels]
      exact levelsBounded_steps ss nIn h ls hwf
  | .lsub _ _ _ _ _ _ _ _ _ :: ss, nIn, .lsub _ _ _ _ _ _ _ _ _ h, ls, hwf => by
      simp only [steps, List.map_cons, PStep.sk, Skels.appLevels]
      exact levelsBounded_steps ss nIn h ls hwf
  | .cctx _ _ _ _ _ _ _ :: ss, nIn, .cctx _ _ _ _ _ _ _ h, ls, hwf => by
      simp only [steps, List.map_cons, PStep.sk, Skels.appLevels]
      exact levelsBounded_steps ss nIn h ls hwf
  | .linst ls0 a nStep hls hlen :: ss, _, .linst _ _ _ _ _ h, ls, hwf => by
      simp only [steps, List.map_cons, PStep.sk, Skels.appLevels]
      exact levelsBounded_steps ss nStep h (ls.map (instLevel ls0))
        (levelsBounded_map_instLevel hls ls (hlen ▸ hwf))

/-- The stored replacement is the outer skeleton applied to the local
replacement. `cctx` does not move a term, so it has no equation. -/
inductive EsInv {E : ResolvedEnv} {n : Nat} : List (PStep E n) → Type where
  | nil : EsInv []
  | wk (c d) (h : EsInv ss) : EsInv (.wk c d :: ss)
  | cctx (p Askel newTy oldTy u Γr hc) (h : EsInv ss) :
      EsInv (.cctx p Askel newTy oldTy u Γr hc :: ss)
  | linst (ls a nStep hls hlen) (h : EsInv ss) :
      EsInv (.linst ls a nStep hls hlen :: ss)
  | esub (j v t Γe Γr hget repl replT hv) (h : EsInv ss)
      (hr : repl = Skels.app (steps ss) (lift 0 j v))
      (hT : replT = Skels.app (steps ss) (lift 0 j t)) :
      EsInv (.esub j v t Γe Γr hget repl replT hv :: ss)
  | lsub (j v t Γe Γr hget repl replT hv) (h : EsInv ss)
      (hr : repl = Skels.app (steps ss) (lift 0 j v))
      (hT : replT = Skels.app (steps ss) (lift 0 j t)) :
      EsInv (.lsub j v t Γe Γr hget repl replT hv :: ss)

theorem get?_cons_succ_assumption {Γ : LCtx} {j : Nat} {t : Expr Nat} {d : LocalDecl}
    (h : Γ.get? j = some (.assumption t)) :
    (d :: Γ).get? (j + 1) = some (.assumption t) := by
  rw [List.get?_cons_succ]; exact h

theorem get?_cons_succ_let {Γ : LCtx} {j : Nat} {t v : Expr Nat} {d : LocalDecl}
    (h : Γ.get? j = some (.letBinding t v)) :
    (d :: Γ).get? (j + 1) = some (.letBinding t v) := by
  rw [List.get?_cons_succ]; exact h

/-- Push one binder through a stored step. `dLocal` is the binder as it
appears in this step's own context. `dFinal` is the binder in the final
context, where every stored typing and stored conversion lives. -/
def shiftStep {n : Nat} (dLocal dFinal : LocalDecl) : PStep E n → PStep E n
  | .wk c decl => .wk (c + 1) decl
  | .esub j v t Γe Γr hget repl replT hv =>
      .esub (j + 1) v t (dLocal :: Γe) (insertAt dFinal 0 Γr)
        (get?_cons_succ_assumption (d := dLocal) hget)
        (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dFinal 0 hv)
  | .lsub j v t Γe Γr hget repl replT hv =>
      .lsub (j + 1) v t (dLocal :: Γe) (insertAt dFinal 0 Γr)
        (get?_cons_succ_let (d := dLocal) hget)
        (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dFinal 0 hv)
  | .linst ls a nStep hls hlen => .linst ls a nStep hls hlen
  | .cctx p Askel newTy oldTy u Γr hc =>
      .cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dFinal 0 Γr)
        (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
          (CvP.wk E n Γr newTy oldTy (.sort u) dFinal 0 hc))

/-- Head is innermost, so the local binder starts raw and is transported by
each step before the next one sees it. The final binder stays fixed. -/
def shiftAll {n : Nat} (dLocal dFinal : LocalDecl) : List (PStep E n) → List (PStep E n)
  | [] => []
  | s :: ss => shiftStep dLocal dFinal s :: shiftAll (Skel.onDecl s.sk dLocal) dFinal ss

theorem steps_shiftAll {n : Nat} (dLocal dFinal : LocalDecl) :
    (ss : List (PStep E n)) →
      steps (shiftAll dLocal dFinal ss) = (steps ss).map Skel.shift
  | [] => rfl
  | .wk c decl :: ss => by
      simp only [shiftAll, steps, List.map_cons, shiftStep, PStep.sk, Skel.shift]
      exact congrArg (List.cons _) (steps_shiftAll _ dFinal ss)
  | .esub j v t Γe Γr hget repl replT hv :: ss => by
      simp only [shiftAll, steps, List.map_cons, shiftStep, PStep.sk, Skel.shift]
      exact congrArg (List.cons _) (steps_shiftAll _ dFinal ss)
  | .lsub j v t Γe Γr hget repl replT hv :: ss => by
      simp only [shiftAll, steps, List.map_cons, shiftStep, PStep.sk, Skel.shift]
      exact congrArg (List.cons _) (steps_shiftAll _ dFinal ss)
  | .linst ls a nStep hls hlen :: ss => by
      simp only [shiftAll, steps, List.map_cons, shiftStep, PStep.sk, Skel.shift]
      exact congrArg (List.cons _) (steps_shiftAll _ dFinal ss)
  | .cctx p Askel newTy oldTy u Γr hc :: ss => by
      simp only [shiftAll, steps, List.map_cons, shiftStep, PStep.sk, Skel.shift]
      exact congrArg (List.cons _) (steps_shiftAll _ dFinal ss)

theorem fuel_shiftAll {n : Nat} (dLocal dFinal : LocalDecl) :
    (ss : List (PStep E n)) → (nIn : Nat) → FuelRel ss nIn →
      FuelRel (shiftAll dLocal dFinal ss) nIn
  | [], _, .nil => .nil
  | .wk c decl :: ss, nIn, .wk _ _ h => by
      simpa [shiftAll, shiftStep] using
        FuelRel.wk (c + 1) decl (fuel_shiftAll _ dFinal ss nIn h)
  | .esub j v t Γe Γr hget repl replT hv :: ss, nIn, .esub _ _ _ _ _ _ _ _ _ h => by
      simpa [shiftAll, shiftStep] using
        FuelRel.esub (j + 1) v t (dLocal :: Γe) (insertAt dFinal 0 Γr)
          (get?_cons_succ_assumption hget)
          (lift 0 1 repl) (lift 0 1 replT)
          (TyP.wk E n Γr repl replT dFinal 0 hv)
          (fuel_shiftAll _ dFinal ss nIn h)
  | .lsub j v t Γe Γr hget repl replT hv :: ss, nIn, .lsub _ _ _ _ _ _ _ _ _ h => by
      simpa [shiftAll, shiftStep] using
        FuelRel.lsub (j + 1) v t (dLocal :: Γe) (insertAt dFinal 0 Γr)
          (get?_cons_succ_let hget)
          (lift 0 1 repl) (lift 0 1 replT)
          (TyP.wk E n Γr repl replT dFinal 0 hv)
          (fuel_shiftAll _ dFinal ss nIn h)
  | .cctx p Askel newTy oldTy u Γr hc :: ss, nIn, .cctx _ _ _ _ _ _ _ h => by
      simpa [shiftAll, shiftStep] using
        FuelRel.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dFinal 0 Γr)
          (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
            (CvP.wk E n Γr newTy oldTy (.sort u) dFinal 0 hc))
          (fuel_shiftAll _ dFinal ss nIn h)
  | .linst ls a nStep hls hlen :: ss, _, .linst _ _ _ _ _ h => by
      simpa [shiftAll, shiftStep] using
        FuelRel.linst ls a nStep hls hlen (fuel_shiftAll _ dFinal ss nStep h)

def esInv_shiftAll {n : Nat} (dLocal dFinal : LocalDecl) :
    (ss : List (PStep E n)) → EsInv ss → EsInv (shiftAll dLocal dFinal ss)
  | [], .nil => .nil
  | .wk c decl :: ss, .wk _ _ h => by
      simpa [shiftAll, shiftStep] using
        EsInv.wk (c + 1) decl (esInv_shiftAll _ dFinal ss h)
  | .cctx p Askel newTy oldTy u Γr hc :: ss, .cctx _ _ _ _ _ _ _ h => by
      simpa [shiftAll, shiftStep] using
        EsInv.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dFinal 0 Γr)
          (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
            (CvP.wk E n Γr newTy oldTy (.sort u) dFinal 0 hc))
          (esInv_shiftAll _ dFinal ss h)
  | .linst ls a nStep hls hlen :: ss, .linst _ _ _ _ _ h => by
      simpa [shiftAll, shiftStep] using
        EsInv.linst ls a nStep hls hlen (esInv_shiftAll _ dFinal ss h)
  | .esub j v t Γe Γr hget repl replT hv :: ss, .esub _ _ _ _ _ _ _ _ _ h hr hT => by
      refine EsInv.esub (j + 1) v t (dLocal :: Γe) (insertAt dFinal 0 Γr)
        (get?_cons_succ_assumption (d := dLocal) hget)
        (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dFinal 0 hv)
        (esInv_shiftAll (Skel.onDecl (PStep.sk (.esub j v t Γe Γr hget repl replT hv)) dLocal)
          dFinal ss h) ?_ ?_
      · show lift 0 1 repl =
            Skels.app (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
              (lift 0 (j + 1) v)
        rw [steps_shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss, hr]
        rw [← lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v,
          ← app_lift0 (steps ss) (lift 0 j v)]
      · show lift 0 1 replT =
            Skels.app (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
              (lift 0 (j + 1) t)
        rw [steps_shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss, hT]
        rw [← lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t,
          ← app_lift0 (steps ss) (lift 0 j t)]
  | .lsub j v t Γe Γr hget repl replT hv :: ss, .lsub _ _ _ _ _ _ _ _ _ h hr hT => by
      refine EsInv.lsub (j + 1) v t (dLocal :: Γe) (insertAt dFinal 0 Γr)
        (get?_cons_succ_let (d := dLocal) hget)
        (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dFinal 0 hv)
        (esInv_shiftAll (Skel.onDecl (PStep.sk (.lsub j v t Γe Γr hget repl replT hv)) dLocal)
          dFinal ss h) ?_ ?_
      · show lift 0 1 repl =
            Skels.app (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
              (lift 0 (j + 1) v)
        rw [steps_shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss, hr]
        rw [← lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v,
          ← app_lift0 (steps ss) (lift 0 j v)]
      · show lift 0 1 replT =
            Skels.app (steps (shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss))
              (lift 0 (j + 1) t)
        rw [steps_shiftAll (Skel.onDecl (.esub j v) dLocal) dFinal ss, hT]
        rw [← lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t,
          ← app_lift0 (steps ss) (lift 0 j t)]

theorem appLevel_shift (ss : List Skel) (l : Level) :
    Skels.appLevel (ss.map Skel.shift) l = Skels.appLevel ss l := by
  induction ss generalizing l with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | wk => simp only [List.map_cons, Skels.appLevel, Skel.shift, ih]
    | esub => simp only [List.map_cons, Skels.appLevel, Skel.shift, ih]
    | linst ls => simp only [List.map_cons, Skels.appLevel, Skel.shift, ih]
    | cctx => simp only [List.map_cons, Skels.appLevel, Skel.shift, ih]

/-- The codomain context after `setAssump` at `k + 1` is the renamed binder
in front of `setAssump` at `k`. -/
theorem ctx_under_binder {n : Nat} (dLocal dFinal : LocalDecl)
    (ss : List (PStep E n)) (A : Expr Nat) (Γ : LCtx) (k : Nat) (Dom' : Expr Nat) :
    setAssump (k + 1) Dom'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (.assumption A :: Γ)) =
      .assumption (Skels.app (steps ss) A) ::
        setAssump k Dom' (Skels.ctx (steps ss) Γ) := by
  rw [steps_shiftAll dLocal dFinal ss, ctx_shift (.assumption A) (steps ss) Γ,
    onDecl_assumption, setAssump_succ]

theorem get?_under_binder {n : Nat} {Dom : Expr Nat} (dLocal dFinal : LocalDecl)
    (ss : List (PStep E n)) (A : Expr Nat) (Γ : LCtx) (k : Nat)
    (hget : (Skels.ctx (steps ss) Γ).get? k = some (.assumption Dom)) :
    (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (.assumption A :: Γ)).get? (k + 1) =
      some (.assumption Dom) := by
  rw [steps_shiftAll dLocal dFinal ss, get?_shift]; exact hget

theorem drop_under_binder {n : Nat} (dLocal dFinal : LocalDecl)
    (ss : List (PStep E n)) (A : Expr Nat) (Γ : LCtx) (k : Nat) :
    (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (.assumption A :: Γ)).drop (k + 2) =
      (Skels.ctx (steps ss) Γ).drop (k + 1) := by
  rw [steps_shiftAll dLocal dFinal ss, drop_shift]

/-- An assumption has no let value. `zetaLocal` on an `esub` hole is
impossible. -/
theorem lookupValue_assumption_none {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (h : Γ.get? i = some (.assumption A)) : lookupValue Γ i = none := by
  unfold lookupValue
  rw [h]

/-- Context threading for `bwalk`. Built with `rfl` at each transport node, so
the hole can rewrite the stored context back to the context the walk has
computed. -/
inductive Run (k : Nat) (Dom' : Expr Nat) {E : ResolvedEnv} {n : Nat} :
    List (PStep E n) → LCtx → Type where
  | nil {Γ : LCtx} : Run k Dom' [] Γ
  | wk {Γ : LCtx} (c : Nat) (d : LocalDecl) {ss : List (PStep E n)}
      (h : Run k Dom' ss (insertAt d c Γ)) : Run k Dom' (.wk c d :: ss) Γ
  | esub {Γ : LCtx} {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx}
      {hget : Γe.get? j = some (.assumption t)} {repl replT : Expr Nat}
      {hv : TyP E n Γr repl replT} {ss : List (PStep E n)}
      (hΓ : Γ = Γe)
      (hctx : Γr = setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (h : Run k Dom' ss (substRemove v j Γ)) :
      Run k Dom' (.esub j v t Γe Γr hget repl replT hv :: ss) Γ
  | lsub {Γ : LCtx} {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx}
      {hget : Γe.get? j = some (.letBinding t v)} {repl replT : Expr Nat}
      {hv : TyP E n Γr repl replT} {ss : List (PStep E n)}
      (hΓ : Γ = Γe)
      (hctx : Γr = setAssump k Dom' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (h : Run k Dom' ss (substRemove v j Γ)) :
      Run k Dom' (.lsub j v t Γe Γr hget repl replT hv :: ss) Γ
  | linst {Γ : LCtx} (ls : List Level) (a nStep : Nat)
      (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
      {ss : List (PStep E n)}
      (h : Run k Dom' ss (instLvlsCtx ls Γ)) :
      Run k Dom' (.linst ls a nStep hls hlen :: ss) Γ
  | cctx {Γ : LCtx} (p : Nat) (Askel newTy oldTy : Expr Nat) (u : Level) {Γr : LCtx}
      {hc : CvP E n Γr newTy oldTy (.sort u)} {ss : List (PStep E n)}
      (Aold : Expr Nat)
      (hdec : Γ.get? p = some (.assumption Aold))
      (hnew : newTy = Skels.app (steps ss) (lift 0 (p + 1) Askel))
      (hold : oldTy = Skels.app (steps ss) (lift 0 (p + 1) Aold))
      (hctx : Γr = setAssump k Dom' (Skels.ctx (steps ss) (setAssump p Askel Γ)))
      (h : Run k Dom' ss (setAssump p Askel Γ)) :
      Run k Dom' (.cctx p Askel newTy oldTy u Γr hc :: ss) Γ

/-- Successive type conversions, each at its own sort. `CvP.trans` needs one
ascribed type, and two `cctx` hits on the same variable need not share a
sort. The consumer applies `TyP.conv` once per link. -/
inductive ConvChain (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Expr Nat → Expr Nat → Type where
  | nil {a : Expr Nat} : ConvChain E n Γ a a
  | cons {a b c : Expr Nat} (u : Level) (h : CvP E n Γ a b (.sort u))
      (rest : ConvChain E n Γ b c) : ConvChain E n Γ a c

def ConvChain.snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c : Expr Nat} :
    ConvChain E n Γ a b → (u : Level) → CvP E n Γ b c (.sort u) → ConvChain E n Γ a c
  | .nil, u, h => .cons u h .nil
  | .cons u1 h1 rest, u, h => .cons u1 h1 (snoc rest u h)

/-- One `TyP.conv` per link. Two `cctx` hits need not share a sort, so this
is not one `CvP.trans`. -/
def ConvChain.apply {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e a c : Expr Nat}
    (h : TyP E n Γ e a) : ConvChain E n Γ a c → TyP E n Γ e c
  | .nil => h
  | .cons (b := b) u hc rest =>
      ConvChain.apply (TyP.conv E n Γ e a b u h hc) rest

/-- What a renamed variable has become. `keep` is still a variable.
`repl` is an `esub` hole, already typed in the final context. `retype`
is one or more `cctx` hits: the lookup is `B` and `hc` sends it to the
ascribed type, one sort per hit. -/
inductive BWalk (E : ResolvedEnv) (n : Nat) (Γfin : LCtx) (term ty : Expr Nat) : Type where
  | keep (Γpre : LCtx) (j : Nat) (hterm : term = .bvar j) (hlook : lookupType Γpre j = some ty)
  | repl (hv : TyP E n Γfin term ty)
  | retype (Γpre : LCtx) (j : Nat) (B : Expr Nat)
      (hterm : term = .bvar j) (hlook : lookupType Γpre j = some B)
      (hc : ConvChain E n Γfin B ty)

def BWalk.cast {n : Nat} {Γfin : LCtx} {term ty term' ty' : Expr Nat}
    (hterm : term = term') (hty : ty = ty') (w : BWalk E n Γfin term ty) :
    BWalk E n Γfin term' ty' :=
  hterm ▸ hty ▸ w

def BWalk.castCtx {n : Nat} {Γfin Γfin' : LCtx} {term ty : Expr Nat}
    (hΓ : Γfin = Γfin') (w : BWalk E n Γfin term ty) : BWalk E n Γfin' term ty :=
  hΓ ▸ w

/-- Walk `.bvar i` through the skeleton. `k` and `Dom'` are the slot
`setAssump` writes; they do not affect the renaming, only the final context. -/
def bwalk {n : Nat} (k : Nat) (Dom' : Expr Nat) :
    (ss : List (PStep E n)) → (i : Nat) → (A : Expr Nat) → (Γ : LCtx) →
      lookupType Γ i = some A → EsInv ss → Run k Dom' ss Γ →
        BWalk E n (setAssump k Dom' (Skels.ctx (steps ss) Γ))
          (Skels.app (steps ss) (.bvar i)) (Skels.app (steps ss) A)
  | [], i, A, Γ, h, _, _ => .keep Γ i rfl h
  | .wk c d :: ss, i, A, Γ, h, .wk _ _ hinv, .wk _ _ hrun =>
      if hi : i < c then
        BWalk.cast (Eq.symm (congrArg (Skels.app (steps ss)) (lift_bvar_lt hi))) rfl
          (bwalk k Dom' ss i (lift c 1 A) (insertAt d c Γ)
            (lookupType_insertAt_lt d hi h) hinv hrun)
      else
        have hic : c ≤ i := Nat.le_of_not_lt hi
        BWalk.cast (Eq.symm (congrArg (Skels.app (steps ss)) (lift_bvar_ge hic))) rfl
          (bwalk k Dom' ss (i + 1) (lift c 1 A) (insertAt d c Γ)
            (lookupType_insertAt_ge d hic h) hinv hrun)
  | .esub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .esub _ _ _ _ _ _ _ _ _ hinv hr hT, .esub hΓ hctx hrun =>
      if hi : i < j then
        BWalk.cast
          (Eq.symm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))) rfl
          (bwalk k Dom' ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_lt hi h) hinv hrun)
      else if hj : j < i then
        BWalk.cast
          (Eq.symm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))) rfl
          (bwalk k Dom' ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
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
        exact BWalk.repl (tyCastCtx hctx (tyCast hterm hty hv))
  | .lsub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .lsub _ _ _ _ _ _ _ _ _ hinv hr hT, .lsub hΓ hctx hrun =>
      if hi : i < j then
        BWalk.cast
          (Eq.symm (congrArg (Skels.app (steps ss)) (instantiate_bvar_lt hi))) rfl
          (bwalk k Dom' ss i (instantiate j (lift 0 j v) A) (substRemove v j Γ)
            (lookupType_substRemove_lt hi h) hinv hrun)
      else if hj : j < i then
        BWalk.cast
          (Eq.symm (congrArg (Skels.app (steps ss)) (instantiate_bvar_gt hj))) rfl
          (bwalk k Dom' ss (i - 1) (instantiate j (lift 0 j v) A) (substRemove v j Γ)
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
        exact BWalk.repl (tyCastCtx hctx (tyCast hterm hty hv))
  | .linst ls a nStep hls hlen :: ss, i, A, Γ, h, .linst _ _ _ _ _ hinv, .linst _ _ _ _ _ hrun =>
      bwalk k Dom' ss i (instantiateLevels ls A) (instLvlsCtx ls Γ)
        (lookupType_instLvlsCtx_some ls h) hinv hrun
  | .cctx p Askel newTy oldTy u Γr hc :: ss, i, A, Γ, h,
      .cctx _ _ _ _ _ _ _ hinv,
      .cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun =>
      if hip : i = p then
        have hdec' : Γ.get? i = some (.assumption Aold) := hip ▸ hdec
        have hAold : A = lift 0 (i + 1) Aold := lookupType_of_assumption hdec' h
        let w := bwalk k Dom' ss p (lift 0 (p + 1) Askel) (setAssump p Askel Γ)
          (lookupType_setAssump_at Askel Γ p (hip ▸ h)) hinv hrun
        have hOld : oldTy = Skels.app (steps ss) A := by
          rw [hold, ← hip, hAold]
        let hc0 := cvCastCtx hctx (cvCast hnew hOld rfl hc)
        match w with
        | .keep Γpre j hterm hlook =>
            .retype Γpre j (Skels.app (steps ss) (lift 0 (p + 1) Askel))
              (hip.symm ▸ hterm) hlook (.cons u hc0 .nil)
        | .repl hv =>
            .repl (tyCast
              (by simp only [steps, List.map_cons, PStep.sk, Skels.app, Skel.app1, hip])
              rfl
              (TyP.conv E n _ _ _ _ u hv hc0))
        | .retype Γpre j B hterm hlook hc' =>
            .retype Γpre j B (hip.symm ▸ hterm) hlook (hc'.snoc u hc0)
      else
        bwalk k Dom' ss i A (setAssump p Askel Γ) (lookupType_setAssump_ne hip h) hinv hrun

end Rcic.Syn
