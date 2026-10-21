import rcic.RcicSynCanon
import rcic.RcicSynHeadView
import rcic.RcicSynPiInv

/-!
# Syntactic sortRow, build step 3w — the β redex, read out of the typing

`research/rcic/semantic/S3_ES_ARMS.md` §22. `es_beta_drop` / `es_beta_rel`
ask for the erasure of `dl`, the typing of `app (lam A body) arg`. A
canonical `app` of a canonical `lam` pays `hbody` and `hbody.reg` side by
side, and that copy can outweigh `CvP.beta`, which paid for `hbody` once.
`cl_under` (a weight bound) does not apply to that canon.

`readLam` / `readRedex` do not rebuild it. They walk the derivation and
return the stored body and the stored argument. `wk`, `esub`, `linst` and
`ewk` are pushed, and each push keeps the atom multiset of the extracted
typing under the source typing's weight: a `wk` adds no atoms, and an
`esub` adds only the replacement atoms the source node already paid for.
`cl_under_atoms` turns that multiset bound into `CL`, via `dmStep_under_rule`.

Two spines return `.no`.

* `cctx`. Pushing it is `tyCctxAt`, and that walk rebuilds rule nodes. The
  atom bound does not survive the rebuild.
* an `esub` whose application already existed and whose function is the
  substituted variable. The λ is the replacement; the argument is the other
  branch of a derivation that is not itself a redex. That split is not this
  reader.

The pure `app` of a pure `lam` returns `.yes`. Its body is the lam's
`hbody` (environment-weakened), not a second typing of the body's type.
Erasure commutation (`lift` / `inst` against the app and lam clauses) is
not in this module. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv}

/-! ## §1 casts do not change the atom multiset -/

theorem atoms_tyCast (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T') (D : TyP E n Γ e T) :
    (tyCast he hT D).atoms Aw = D.atoms Aw := by
  cases he
  cases hT
  rfl

theorem atoms_tyCastCtx (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    {e T : Expr Nat} (hΓ : Γ = Γ') (D : TyP E n Γ e T) :
    (tyCastCtx hΓ D).atoms Aw = D.atoms Aw := by
  cases hΓ
  rfl

theorem instLvls_assumption (ls : List Level) (A₀ : Expr Nat) (Γ₀ : LCtx) :
    instLvlsCtx ls (.assumption A₀ :: Γ₀) =
      .assumption (instantiateLevels ls A₀) :: instLvlsCtx ls Γ₀ := rfl

theorem atoms_esub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} (D : TyP E n Γ e A)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).atoms Aw
      = D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw := rfl

/-! ## §2 what a λ-typing yields -/

/-- The body of a typing of `.lam A body`, at the conclusion context.
    Every atom of that body typing sits strictly under `src`. -/
structure LamGot (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A body : Expr Nat) : Type where
  B : Expr Nat
  u : Level
  hbody : TyP E n (.assumption A :: Γ) body B
  lt : ∀ y ∈ hbody.atoms Aw, y < src

/-- `.no` is a spine this reader does not push (`cctx`, or an application
    born around a substituted λ). -/
inductive LamRead (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A body : Expr Nat) : Type where
  | yes (g : LamGot Aw src E n Γ A body)
  | no

def LamRead.isYes {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body : Expr Nat} : LamRead Aw src E n Γ A body → Bool
  | .yes _ => true
  | .no => false

def LamRead.raise {Aw : Nat → Nat} {src src' : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body : Expr Nat} (h : src < src')
    (r : LamRead Aw src E n Γ A body) : LamRead Aw src' E n Γ A body :=
  match r with
  | .no => .no
  | .yes g => .yes { g with lt := fun y hy => Nat.lt_trans (g.lt y hy) h }

/-- Push `wk` under the λ. The body moves one cutoff deeper. Atoms are unchanged. -/
def pushLamWk {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ : Expr Nat} (d : LocalDecl) (c : Nat)
    (r : LamRead Aw src E n Γ₀ A₀ b₀) {A body : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) :
    LamRead Aw src E n (insertAt d c Γ₀) A body :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        B := lift (c + 1) 1 g.B
        u := g.u
        hbody :=
          tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))
        lt := by
          intro y hy
          rw [atoms_tyCastCtx, atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.lt y hy }

/-- Push `linst` under the λ. Levels in the body are instantiated; atoms are not. -/
def pushLamLinst {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (r : LamRead Aw src E a Γ₀ A₀ b₀) {A body : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body) :
    LamRead Aw src E n (instLvlsCtx ls Γ₀) A body :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        B := instantiateLevels ls g.B
        u := instLevel ls g.u
        hbody :=
          tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
              (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
            (tyCast hb rfl
              (TyP.linst E a n (.assumption A₀ :: Γ₀) b₀ g.B ls hls hlen g.hbody))
        lt := by
          intro y hy
          rw [atoms_tyCastCtx, atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.lt y hy }

/-- Push `esub` under the binder, the body half of `piEsub`. -/
def pushBodyEsub {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body) :
    TyP E n (.assumption A :: substRemove repl j Γ₀) body
      (instantiate (j + 1) (lift 0 (j + 1) repl) B₀) :=
  let Γ := substRemove repl j Γ₀
  let hctx := (substRemove_cod_eq repl j A₀ A Γ₀ hAe).symm
  let hv1 := TyP.wk E n Γ (lift 0 j repl) (lift 0 j t) (.assumption A) 0 hv
  let hv2 := tyCast
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) repl)
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t) hv1
  let hv3 := tyCastCtx hctx hv2
  let hvT1 := TyP.wk E n Γ (lift 0 j t) (.sort uE) (.assumption A) 0 hvT
  let hvT2 := tyCast
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t) rfl hvT1
  let hvT3 := tyCastCtx hctx hvT2
  let hget' := hget_succ (d := .assumption A₀) hget
  let cod0 := TyP.esub E n (.assumption A₀ :: Γ₀) b₀ B₀ t repl (j + 1) uE
    hbody hget' hv3 hvT3
  let cod1 := tyCast (instantiate_succ_merge j repl b₀ body hBe) rfl cod0
  tyCastCtx (substRemove_cod_eq repl j A₀ A Γ₀ hAe) cod1

theorem atoms_pushBodyEsub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body) :
    (pushBodyEsub hbody hget hv hvT hAe hBe).atoms Aw
      = hbody.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw := by
  unfold pushBodyEsub
  simp only [atoms_tyCastCtx, atoms_tyCast, TyP.atoms]

/-- `esub` of a λ. The extracted body pays the inner body plus the replacement,
    which is what the source `esub` node already pays. `w` is that node's weight. -/
def pushLamEsub {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {src : Nat} {n : Nat} {Γ₀ : LCtx} {A₀ b₀ t repl : Expr Nat}
    {j : Nat} {uE : Level}
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (r : LamRead Aw src E n Γ₀ A₀ b₀) {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (w : Nat) (hsrc : src < w) (hvw : hv.wt Aw < w) (hvTw : hvT.wt Aw < w) :
    LamRead Aw w E n (substRemove repl j Γ₀) A body :=
  match r with
  | .no => .no
  | .yes g =>
      let hvE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv
      let hvTE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT
      .yes {
        B := instantiate (j + 1) (lift 0 (j + 1) repl) g.B
        u := g.u
        hbody := pushBodyEsub g.hbody hget hvE hvTE hAe hBe
        lt := by
          intro y hy
          have hat := atoms_pushBodyEsub Aw g.hbody hget hvE hvTE hAe hBe
          have hy' : y ∈ g.hbody.atoms Aw ++ hvE.atoms Aw ++ hvTE.atoms Aw := hat.symm ▸ hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy'
          cases List.mem_append.mp hy' with
          | inl hy' =>
            cases List.mem_append.mp hy' with
            | inl hyb => exact Nat.lt_trans (g.lt y hyb) hsrc
            | inr hyv => exact atoms_lt_of_wt_lt Aw hv hvw y hyv
          | inr hyT => exact atoms_lt_of_wt_lt Aw hvT hvTw y hyT }

/-- Read a typing of `.lam A body`. The result is at `E`, and on `.yes` every
    atom of the body is `< D.wt`. -/
def readLam {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A body : Expr Nat} → (he : e = .lam A body) →
    LamRead Aw (D.wt Aw) E n Γ A body
  | _, _, _, _, .sort .., _, _, he => by cases he
  | _, _, _, _, .bvar .., _, _, he => by cases he
  | _, _, _, _, .const .., _, _, he => by cases he
  | _, _, _, _, .pi .., _, _, he => by cases he
  | n, Γ, _, _, .lam _ _ _ A₀ u body₀ B v hA hbody hB, A, body, he =>
      match A₀, body₀, hbody, he with
      | _, _, hbody', rfl =>
          .yes {
            B := B
            u := u
            hbody := TyP.ewk Ei E n (.assumption A :: Γ) body B hext hbody'
            lt := by
              intro y hy
              simp only [TyP.atoms] at hy
              exact atoms_lt_of_wt_lt Aw hbody'
                (by simp only [TyP.wt]; omega) y hy }
  | _, _, _, _, .app .., _, _, he => by cases he
  | _, _, _, _, .letE .., _, _, he => by cases he
  | _, _, _, _, .lit .., _, _, he => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner _, _, _, he =>
      LamRead.raise (by simp only [TyP.wt]; omega) (readLam hext Aw inner he)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he =>
      match lift_eq_lam he with
      | .mk A₀ b₀ he₀ hAe hb₀ =>
          LamRead.raise (by simp only [TyP.wt]; omega)
            (pushLamWk d c (readLam hext Aw inner he₀) hAe hb₀)
  | n, _, _, _, .esub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he =>
      match instantiate_eq_lam he with
      | .under A₀ b₀ he₀ hAe hb₀ =>
          pushLamEsub hext Aw hget hv hvT
            (readLam hext Aw inner he₀) hAe hb₀
            ((TyP.esub Ei n Γ₀ _ _ t repl j uE inner hget hv hvT).wt Aw)
            (by simp only [TyP.wt]; omega)
            (by simp only [TyP.wt]; omega)
            (by simp only [TyP.wt]; omega)
      | .here _ hr =>
          LamRead.raise (by simp only [TyP.wt]; omega) (readLam hext Aw hv hr)
  | _, _, _, _, .lsub .., _, _, _ => .no
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he =>
      match instantiateLevels_eq_lam he with
      | .mk A₀ b₀ he₀ hAe hb₀ =>
          LamRead.raise (by simp only [TyP.wt]; omega)
            (pushLamLinst ls hls hlen (readLam hext Aw inner he₀) hAe hb₀)
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, he =>
      LamRead.raise (by simp only [TyP.wt]; omega)
        (readLam (envExt_trans hext' hext) Aw inner he)
  | _, _, _, _, .cctx .., _, _, _ => .no

/-- A pure λ node is `.yes`. The body is `hbody`, environment-weakened. -/
theorem readLam_lam_yes (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    (readLam (envExt_refl E) Aw
      (TyP.lam E n Γ A u body B v hA hbody hB) rfl).isYes = true := by
  rfl

/-! ## §3 what an `app (lam …)` typing yields -/

/-- Body and argument of a typing of `.app (.lam A body) arg`. The argument's
    ascribed type is whatever the application recorded; `CL` does not require
    it to be `A`. -/
structure RedexGot (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A body arg : Expr Nat) : Type where
  B : Expr Nat
  u : Level
  Aarg : Expr Nat
  hbody : TyP E n (.assumption A :: Γ) body B
  harg : TyP E n Γ arg Aarg
  ltB : ∀ y ∈ hbody.atoms Aw, y < src
  ltA : ∀ y ∈ harg.atoms Aw, y < src

inductive RedexRead (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A body arg : Expr Nat) : Type where
  | yes (g : RedexGot Aw src E n Γ A body arg)
  | no

def RedexRead.isYes {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg : Expr Nat} :
    RedexRead Aw src E n Γ A body arg → Bool
  | .yes _ => true
  | .no => false

def RedexRead.raise {Aw : Nat → Nat} {src src' : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg : Expr Nat} (h : src < src')
    (r : RedexRead Aw src E n Γ A body arg) :
    RedexRead Aw src' E n Γ A body arg :=
  match r with
  | .no => .no
  | .yes g => .yes { g with
      ltB := fun y hy => Nat.lt_trans (g.ltB y hy) h
      ltA := fun y hy => Nat.lt_trans (g.ltA y hy) h }

theorem app_of_lam {e f a A₀ b₀ : Expr Nat}
    (he : e = .app f a) (hf : f = .lam A₀ b₀) : e = .app (.lam A₀ b₀) a := by
  subst he
  subst hf
  rfl

/-- The application node. The function's reader supplies the body; the
    argument is the node's own `ha`. -/
def redexOfApp {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {n : Nat} {Γ : LCtx} {A body arg A₀ B₀ : Expr Nat} {w : Level}
    {hf : TyP Ei n Γ (.lam A body) (.pi A₀ B₀)}
    (g : LamGot Aw (hf.wt Aw) E n Γ A body)
    (ha : TyP Ei n Γ arg A₀)
    (hT : TyP Ei n Γ (instantiate0 arg B₀) (.sort w)) :
    RedexGot Aw ((TyP.app Ei n Γ (.lam A body) arg A₀ B₀ w hf ha hT).wt Aw)
      E n Γ A body arg :=
  { B := g.B
    u := g.u
    Aarg := A₀
    hbody := g.hbody
    harg := TyP.ewk Ei E n Γ arg A₀ hext ha
    ltB := fun y hy =>
      Nat.lt_trans (g.lt y hy) (by simp only [TyP.wt]; omega)
    ltA := by
      intro y hy
      simp only [TyP.atoms] at hy
      exact atoms_lt_of_wt_lt Aw ha (by simp only [TyP.wt]; omega) y hy }

def pushRedexWk {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ a₀ : Expr Nat} (d : LocalDecl) (c : Nat)
    (r : RedexRead Aw src E n Γ₀ A₀ b₀ a₀) {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body)
    (ha : lift c 1 a₀ = arg) :
    RedexRead Aw src E n (insertAt d c Γ₀) A body arg :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        B := lift (c + 1) 1 g.B
        u := g.u
        Aarg := lift c 1 g.Aarg
        hbody :=
          tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hb rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) b₀ g.B d (c + 1) g.hbody))
        harg := tyCast ha rfl (TyP.wk E n Γ₀ a₀ g.Aarg d c g.harg)
        ltB := by
          intro y hy
          rw [atoms_tyCastCtx, atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltB y hy
        ltA := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltA y hy }

def pushRedexLinst {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ a₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (r : RedexRead Aw src E a Γ₀ A₀ b₀ a₀) {A body arg : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
    (ha : instantiateLevels ls a₀ = arg) :
    RedexRead Aw src E n (instLvlsCtx ls Γ₀) A body arg :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        B := instantiateLevels ls g.B
        u := instLevel ls g.u
        Aarg := instantiateLevels ls g.Aarg
        hbody :=
          tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
              (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
            (tyCast hb rfl
              (TyP.linst E a n (.assumption A₀ :: Γ₀) b₀ g.B ls hls hlen g.hbody))
        harg := tyCast ha rfl
          (TyP.linst E a n Γ₀ a₀ g.Aarg ls hls hlen g.harg)
        ltB := by
          intro y hy
          rw [atoms_tyCastCtx, atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltB y hy
        ltA := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltA y hy }

def pushRedexEsub {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {src : Nat} {n : Nat} {Γ₀ : LCtx} {A₀ b₀ a₀ t repl : Expr Nat}
    {j : Nat} {uE : Level}
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (r : RedexRead Aw src E n Γ₀ A₀ b₀ a₀) {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (w : Nat) (hsrc : src < w) (hvw : hv.wt Aw < w) (hvTw : hvT.wt Aw < w) :
    RedexRead Aw w E n (substRemove repl j Γ₀) A body arg :=
  match r with
  | .no => .no
  | .yes g =>
      let hvE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv
      let hvTE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT
      let harg := tyCast haEq rfl
        (TyP.esub E n Γ₀ a₀ g.Aarg t repl j uE g.harg hget hvE hvTE)
      .yes {
        B := instantiate (j + 1) (lift 0 (j + 1) repl) g.B
        u := g.u
        Aarg := instantiate j (lift 0 j repl) g.Aarg
        hbody := pushBodyEsub g.hbody hget hvE hvTE hAe hBe
        harg := harg
        ltB := by
          intro y hy
          have hat := atoms_pushBodyEsub Aw g.hbody hget hvE hvTE hAe hBe
          have hy' : y ∈ g.hbody.atoms Aw ++ hvE.atoms Aw ++ hvTE.atoms Aw :=
            hat.symm ▸ hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy'
          cases List.mem_append.mp hy' with
          | inl hy' =>
            cases List.mem_append.mp hy' with
            | inl hyb => exact Nat.lt_trans (g.ltB y hyb) hsrc
            | inr hyv => exact atoms_lt_of_wt_lt Aw hv hvw y hyv
          | inr hyT => exact atoms_lt_of_wt_lt Aw hvT hvTw y hyT
        ltA := by
          intro y hy
          rw [atoms_tyCast, atoms_esub] at hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy
          cases List.mem_append.mp hy with
          | inl hy =>
            cases List.mem_append.mp hy with
            | inl hya => exact Nat.lt_trans (g.ltA y hya) hsrc
            | inr hyv => exact atoms_lt_of_wt_lt Aw hv hvw y hyv
          | inr hyT => exact atoms_lt_of_wt_lt Aw hvT hvTw y hyT }

/-- Read a typing of `.app (.lam A body) arg`. -/
def readRedex {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A body arg : Expr Nat} → (he : e = .app (.lam A body) arg) →
    RedexRead Aw (D.wt Aw) E n Γ A body arg
  | _, _, _, _, .sort .., _, _, _, he => by cases he
  | _, _, _, _, .bvar .., _, _, _, he => by cases he
  | _, _, _, _, .const .., _, _, _, he => by cases he
  | _, _, _, _, .pi .., _, _, _, he => by cases he
  | _, _, _, _, .lam .., _, _, _, he => by cases he
  | _, _, _, _, .app _ _ _ f a A₀ B₀ w hf ha hT, _, _, _, he =>
      match f, a, he with
      | _, _, rfl =>
          match readLam hext Aw hf rfl with
          | .no => .no
          | .yes g => .yes (redexOfApp hext Aw g ha hT)
  | _, _, _, _, .letE .., _, _, _, he => by cases he
  | _, _, _, _, .lit .., _, _, _, he => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner _, _, _, _, he =>
      RedexRead.raise (by simp only [TyP.wt]; omega) (readRedex hext Aw inner he)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, _, he =>
      match lift_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          match lift_eq_lam hf₀ with
          | .mk A₀ b₀ heLam hAe hb₀ =>
              RedexRead.raise (by simp only [TyP.wt]; omega)
                (pushRedexWk d c
                  (readRedex hext Aw inner (app_of_lam he₀ heLam)) hAe hb₀ ha₀)
  | n, _, _, _, .esub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, _, he =>
      match instantiate_eq_app he with
      | .under f₀ a₀ he₀ hf₀ ha₀ =>
          match instantiate_eq_lam hf₀ with
          | .under A₀ b₀ heLam hAe hb₀ =>
              pushRedexEsub hext Aw hget hv hvT
                (readRedex hext Aw inner (app_of_lam he₀ heLam)) hAe hb₀ ha₀
                ((TyP.esub Ei n Γ₀ _ _ t repl j uE inner hget hv hvT).wt Aw)
                (by simp only [TyP.wt]; omega)
                (by simp only [TyP.wt]; omega)
                (by simp only [TyP.wt]; omega)
          | .here _ _ => .no
      | .here _ hr =>
          RedexRead.raise (by simp only [TyP.wt]; omega)
            (readRedex hext Aw hv hr)
  | _, _, _, _, .lsub .., _, _, _, _ => .no
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, _, he =>
      match instantiateLevels_eq_app he with
      | .mk f₀ a₀ he₀ hf₀ ha₀ =>
          match instantiateLevels_eq_lam hf₀ with
          | .mk A₀ b₀ heLam hAe hb₀ =>
              RedexRead.raise (by simp only [TyP.wt]; omega)
                (pushRedexLinst ls hls hlen
                  (readRedex hext Aw inner (app_of_lam he₀ heLam)) hAe hb₀ ha₀)
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, _, he =>
      RedexRead.raise (by simp only [TyP.wt]; omega)
        (readRedex (envExt_trans hext' hext) Aw inner he)
  | _, _, _, _, .cctx .., _, _, _, _ => .no

def redexRead (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {A body arg T : Expr Nat}
    (D : TyP E n Γ (.app (.lam A body) arg) T) :
    RedexRead Aw (D.wt Aw) E n Γ A body arg :=
  readRedex (envExt_refl E) Aw D rfl

/-- A pure `app` of a pure `lam` is `.yes`. -/
theorem readRedex_app_yes (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    {arg : Expr Nat} {w : Level}
    (ha : TyP E n Γ arg A)
    (hT : TyP E n Γ (instantiate0 arg B) (.sort w)) :
    (readRedex (envExt_refl E) Aw
      (TyP.app E n Γ (.lam A body) arg A B w
        (TyP.lam E n Γ A u body B v hA hbody hB) ha hT) rfl).isYes = true := by
  rfl

/-! ## §4 `CL` from an atom bound -/

/-- `CL` of two typings whose atoms, not their weights, sit under one
    non-transport node. A pushed `wk` of the replacement adds weight and no
    atoms; `cl_under` does not apply to that typing, and this does. -/
theorem cl_under_atoms (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (B : Below Aw tbl (cvMeas Aw hnode))
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E' n' Γ' e T₁) (D₂ : TyP E' n' Γ' e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E' n' Γ' ρ)
    (h₁ : ∀ y ∈ D₁.atoms Aw, y < hnode.wt Aw)
    (h₂ : ∀ y ∈ D₂.atoms Aw, y < hnode.wt Aw) :
    CL tbl σ ρ D₁ D₂ :=
  B.cl D₁ D₂ σ ρ hρ (lex_of_dm (dmStep_under_rule Aw hnode ht
    (Y := D₁.atoms Aw ++ D₂.atoms Aw)
    (fun y hy => by
      cases List.mem_append.mp hy with
      | inl hy => exact h₁ y hy
      | inr hy => exact h₂ y hy)))

/-- `BitCoh` of two sort-typings whose atoms sit under one non-transport node. -/
theorem bitCoh_under_atoms (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (B : Below Aw tbl (cvMeas Aw hnode))
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E' n' Γ' e (.sort u₁)) (D₂ : TyP E' n' Γ' e (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E' n' Γ' ρ)
    (h₁ : ∀ y ∈ D₁.atoms Aw, y < hnode.wt Aw)
    (h₂ : ∀ y ∈ D₂.atoms Aw, y < hnode.wt Aw) :
    BitCoh σ D₁ D₂ :=
  B.bitCoh D₁ D₂ σ ρ hρ (lex_of_dm (dmStep_under_rule Aw hnode ht
    (Y := D₁.atoms Aw ++ D₂.atoms Aw)
    (fun y hy => by
      cases List.mem_append.mp hy with
      | inl hy => exact h₁ y hy
      | inr hy => exact h₂ y hy)))

/-! ## §5 the keep clause of a λ -/

theorem eps_lam_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {body B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)} {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) :
    (TyP.lam E n Γ A u body B v hA hbody hB).eps σ ρ =
      match hbody.eps σ (.keep :: ρ) with
      | .star => .star
      | eb => .lam eb := by
  simp only [TyP.eps, hu]
  rfl

#print axioms instLvls_assumption
#print axioms atoms_tyCast
#print axioms atoms_tyCastCtx
#print axioms atoms_esub
#print axioms atoms_pushBodyEsub
#print axioms readLam_lam_yes
#print axioms app_of_lam
#print axioms readRedex_app_yes
#print axioms cl_under_atoms
#print axioms bitCoh_under_atoms
#print axioms eps_lam_keep
#print axioms pushBodyEsub
#print axioms pushLamEsub
#print axioms readLam
#print axioms redexOfApp
#print axioms pushRedexEsub
#print axioms readRedex
#print axioms redexRead

end Rcic.Syn
