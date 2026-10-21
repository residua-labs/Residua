import rcic.RcicSynRedex
import rcic.RcicSynLetInline

/-!
# `RcicSynSRLitPiRedexAP` — `readRedex` preserves `AssumpPref` (cc 00:40Z)

The row-2 issuance row `IssuesSR.beta_cl_body` reads its `RedexGot` off the
`.es` node's `dl`; for the landed-`Issues`-style AP side condition
(`Issues.ap` per row) the closer must know the READ's two extracted typings
inherit `dl.AssumpPref`. This module proves it:

* `LamRead.apBody` / `RedexRead.apBoth` — the AP content of a read result,
  `True` at `.no` (so every `.no` arm is closed by `trivial`);
* `LamRead.apBody_raise` — `raise` preserves `apBody` (record override
  never touches `hbody`/`harg`, definitional);
* `assumptionPrefix_cons` — `AssumptionPrefix Γ c →
  AssumptionPrefix (.assumption A :: Γ) (c + 1)`, the one context fact the
  `wk`/`esub` pushes need (their re-wrapped nodes sit one binder deeper);
* per-push AP lemmas (`pushLamWk_apBody` … `pushRedexEsub_apBoth`) — each
  push's re-wrapped `hbody`/`harg` inherit AP from the inner read plus the
  node's own prefix, via the LANDED `assumpPref_tyCast`/`_tyCastCtx`;
* `lamRead_ap` / `redexRead_ap` — the spine inductions, mirroring the
  landed `readLam`/`readRedex` arms exactly (composition: every arm is the
  corresponding push lemma applied to the recursive read's `apBody`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the AP content of a read result -/

/-- The body half of `AssumpPref` for a `LamRead`'s yield. -/
def LamRead.apBody {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body : Expr Nat} :
    LamRead Aw src E n Γ A body → Prop
  | .yes g => g.hbody.AssumpPref
  | .no => True

/-- Both extracted typings of a `RedexRead`'s yield. -/
def RedexRead.apBoth {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg : Expr Nat} :
    RedexRead Aw src E n Γ A body arg → Prop
  | .yes g => g.hbody.AssumpPref ∧ g.harg.AssumpPref
  | .no => True

/-- `raise` overrides only the measure fields — the AP content is
    definitionally preserved. -/
theorem LamRead.apBody_raise {Aw : Nat → Nat} {src src' : Nat} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A body : Expr Nat} (h : src < src')
    (r : LamRead Aw src E n Γ A body) :
    (r.raise h).apBody = r.apBody := by
  cases r with
  | yes g => rfl
  | no => rfl

/-- Same for `RedexRead`. -/
theorem RedexRead.apBoth_raise {Aw : Nat → Nat} {src src' : Nat} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A body arg : Expr Nat} (h : src < src')
    (r : RedexRead Aw src E n Γ A body arg) :
    (r.raise h).apBoth = r.apBoth := by
  cases r with
  | yes g => rfl
  | no => rfl

/-- The one context fact the `wk`/`esub` pushes need: one binder deeper,
    one cutoff higher. -/
theorem assumptionPrefix_cons {Γ : LCtx} {c : Nat} {A : Expr Nat}
    (h : AssumptionPrefix Γ c) : AssumptionPrefix (.assumption A :: Γ) (c + 1) := by
  intro d hd
  simp only [List.take_succ_cons] at hd
  rcases List.mem_cons.mp hd with hd | hd
  · exact ⟨A, hd⟩
  · exact h d hd

/-! ## §2 the pushes inherit AP -/

/-- `pushLamWk`: the re-wrapped body is `tyCastCtx ∘ tyCast ∘ wk` one
    binder deeper — the prefix is one cutoff higher, the body AP is the
    inner read's. -/
theorem pushLamWk_apBody {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ : Expr Nat} (d : LocalDecl) (c : Nat)
    (r : LamRead Aw src E n Γ₀ A₀ b₀) {A body : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body)
    (hap : AssumptionPrefix Γ₀ c) (hr : r.apBody) :
    (pushLamWk d c r hA hb).apBody := by
  unfold pushLamWk
  cases r with
  | no => trivial
  | yes g =>
      show (tyCastCtx _ _).AssumpPref
      exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
        ⟨assumptionPrefix_cons hap, hr⟩)

/-- `pushLamLinst`: `linst` AP is the inner AP verbatim. -/
theorem pushLamLinst_apBody {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (r : LamRead Aw src E a Γ₀ A₀ b₀) {A body : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
    (hr : r.apBody) :
    (pushLamLinst ls hls hlen r hA hb).apBody := by
  unfold pushLamLinst
  cases r with
  | no => trivial
  | yes g =>
      show (tyCastCtx _ _).AssumpPref
      exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ hr)

/-- `pushBodyEsub`: the `.esub` sits one binder deeper (`j+1`, one prefix
    higher); the two replacement legs are `wk`-at-0 re-wraps (prefix at 0
    is trivial) under `tyCast`/`tyCastCtx`. -/
theorem pushBodyEsub_ap {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (hapΓ : AssumptionPrefix Γ₀ j) (hapb : hbody.AssumpPref)
    (hapv : hv.AssumpPref) (hapvT : hvT.AssumpPref) :
    (pushBodyEsub hbody hget hv hvT hAe hBe).AssumpPref := by
  unfold pushBodyEsub
  exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
    ⟨assumptionPrefix_cons hapΓ, hapb,
      assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
        ⟨assumptionPrefix_zero _, hapv⟩),
      assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
        ⟨assumptionPrefix_zero _, hapvT⟩)⟩)

/-- `pushLamEsub`: the body half is `pushBodyEsub` at the `ewk`-wrapped
    replacement legs (whose AP is the original `hv`/`hvT`'s). -/
theorem pushLamEsub_apBody {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {src : Nat} {n : Nat} {Γ₀ : LCtx} {A₀ b₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (r : LamRead Aw src E n Γ₀ A₀ b₀) {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (w : Nat) (hsrc : src < w) (hvw : hv.wt Aw < w) (hvTw : hvT.wt Aw < w)
    (hapΓ : AssumptionPrefix Γ₀ j) (hr : r.apBody)
    (hapv : hv.AssumpPref) (hapvT : hvT.AssumpPref) :
    (pushLamEsub hext Aw hget hv hvT r hAe hBe w hsrc hvw hvTw).apBody := by
  unfold pushLamEsub
  cases r with
  | no => trivial
  | yes g => exact pushBodyEsub_ap g.hbody hget _ _ hAe hBe hapΓ hr hapv hapvT

/-! ## §3 the redex pushes -/

/-- `pushRedexWk`: the body one binder deeper (cons prefix), the argument
    at the node's own cutoff. -/
theorem pushRedexWk_apBoth {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ a₀ : Expr Nat} (d : LocalDecl) (c : Nat)
    (r : RedexRead Aw src E n Γ₀ A₀ b₀ a₀) {A body arg : Expr Nat}
    (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body)
    (ha : lift c 1 a₀ = arg)
    (hap : AssumptionPrefix Γ₀ c) (hr : r.apBoth) :
    (pushRedexWk d c r hA hb ha).apBoth := by
  cases r with
  | no => simp only [pushRedexWk, RedexRead.apBoth]
  | yes g =>
      simp only [pushRedexWk, RedexRead.apBoth]
      exact ⟨assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
          ⟨assumptionPrefix_cons hap, hr.1⟩),
        assumpPref_tyCast _ _ ⟨hap, hr.2⟩⟩

/-- `pushRedexLinst`: both legs are `linst` re-wraps — inner AP verbatim. -/
theorem pushRedexLinst_apBoth {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ₀ : LCtx} {A₀ b₀ a₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (r : RedexRead Aw src E a Γ₀ A₀ b₀ a₀) {A body arg : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
    (ha : instantiateLevels ls a₀ = arg) (hr : r.apBoth) :
    (pushRedexLinst ls hls hlen r hA hb ha).apBoth := by
  cases r with
  | no => simp only [pushRedexLinst, RedexRead.apBoth]
  | yes g =>
      simp only [pushRedexLinst, RedexRead.apBoth]
      exact ⟨assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ hr.1),
        assumpPref_tyCast _ _ hr.2⟩

/-- `pushRedexEsub`: the body via `pushBodyEsub` (one binder deeper), the
    argument at the node's own `j` — both replacement legs `ewk`-wrapped
    (AP unchanged). -/
theorem pushRedexEsub_apBoth {Ei : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {src : Nat} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ a₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (r : RedexRead Aw src E n Γ₀ A₀ b₀ a₀) {A body arg : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (haEq : instantiate j (lift 0 j repl) a₀ = arg)
    (w : Nat) (hsrc : src < w) (hvw : hv.wt Aw < w) (hvTw : hvT.wt Aw < w)
    (hapΓ : AssumptionPrefix Γ₀ j) (hr : r.apBoth)
    (hapv : hv.AssumpPref) (hapvT : hvT.AssumpPref) :
    (pushRedexEsub hext Aw hget hv hvT r hAe hBe haEq w hsrc hvw hvTw).apBoth := by
  unfold pushRedexEsub
  cases r with
  | no => simp only [RedexRead.apBoth]
  | yes g =>
      simp only [RedexRead.apBoth]
      exact ⟨pushBodyEsub_ap g.hbody hget _ _ hAe hBe hapΓ hr.1 hapv hapvT,
        assumpPref_tyCast _ _ ⟨hapΓ, hr.2, hapv, hapvT⟩⟩

/-- `redexOfApp`: the extracted body is the lam-read's own, the argument is
    an `ewk` re-wrap of the node's own `ha`. -/
theorem redexOfApp_apBoth {Ei : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {A body arg A₀ B₀ : Expr Nat}
    {w : Level} {hf : TyP Ei n Γ (.lam A body) (.pi A₀ B₀)}
    (g : LamGot Aw (hf.wt Aw) E n Γ A body)
    (ha : TyP Ei n Γ arg A₀)
    (hT : TyP Ei n Γ (instantiate0 arg B₀) (.sort w))
    (hapb : g.hbody.AssumpPref) (hapa : ha.AssumpPref) :
    (redexOfApp hext Aw g ha hT).hbody.AssumpPref ∧
      (redexOfApp hext Aw g ha hT).harg.AssumpPref := by
  simp only [redexOfApp]
  exact ⟨hapb, hapa⟩

/-! ## §4 the spine inductions -/

/-- `readLam` preserves the body's `AssumpPref`: each arm is the
    corresponding push lemma applied to the recursive read's `apBody`. -/
theorem lamRead_ap {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) :
    {n : Nat}→ {Γ : LCtx}→ {e T : Expr Nat}→ (D : TyP Ei n Γ e T) →
    {A body : Expr Nat}→ (he : e = .lam A body) → D.AssumpPref →
    (readLam hext Aw D he).apBody
  | _, _, _, _, .sort .., _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _ => by cases he
  | _, _, _, _, .pi .., _, _, he, _ => by cases he
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hbody _, _, _, he, hap => by
      cases he
      simp only [readLam, LamRead.apBody]
      exact hap.2.1
  | _, _, _, _, .app .., _, _, he, _ => by cases he
  | _, _, _, _, .letE .., _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner _, _, _, he, hap => by
      simp only [readLam]
      rw [LamRead.apBody_raise]
      exact lamRead_ap hext Aw inner he hap.1
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, hap => by
      dsimp only [readLam]
      cases lift_eq_lam he with
      | mk _ _ he₀ hAe hb₀ =>
          show (LamRead.raise _ (pushLamWk d c (readLam hext Aw inner he₀)
            hAe hb₀)).apBody
          rw [LamRead.apBody_raise]
          exact pushLamWk_apBody d c _ hAe hb₀ hap.1
            (lamRead_ap hext Aw inner he₀ hap.2)
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, hap => by
      dsimp only [readLam]
      cases instantiate_eq_lam he with
      | under _ _ he₀ hAe hb₀ =>
          show (pushLamEsub hext Aw hget hv hvT (readLam hext Aw inner he₀)
            hAe hb₀ _ _ _ _).apBody
          exact pushLamEsub_apBody hext Aw hget hv hvT _ hAe hb₀ _ _ _ _
            hap.1 (lamRead_ap hext Aw inner he₀ hap.2.1) hap.2.2.1 hap.2.2.2
      | here _ hr =>
          show (LamRead.raise _ (readLam hext Aw hv hr)).apBody
          rw [LamRead.apBody_raise]
          exact lamRead_ap hext Aw hv hr hap.2.2.1
  | _, _, _, _, .lsub .., _, _, _, _ => by
      simp only [readLam, LamRead.apBody]
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, hap => by
      dsimp only [readLam]
      cases instantiateLevels_eq_lam he with
      | mk _ _ he₀ hAe hb₀ =>
          show (LamRead.raise _ (pushLamLinst ls hls hlen
            (readLam hext Aw inner he₀) hAe hb₀)).apBody
          rw [LamRead.apBody_raise]
          exact pushLamLinst_apBody ls hls hlen _ hAe hb₀
            (lamRead_ap hext Aw inner he₀ hap)
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, he, hap => by
      simp only [readLam]
      rw [LamRead.apBody_raise]
      exact lamRead_ap (envExt_trans hext' hext) Aw inner he hap
  | _, _, _, _, .cctx .., _, _, _, _ => by
      simp only [readLam, LamRead.apBody]

/-- `readRedex` preserves both extracted typings' `AssumpPref` — the row-2
    issuance row's AP side condition. -/
theorem redexRead_ap {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) :
    {n : Nat}→ {Γ : LCtx}→ {e T : Expr Nat}→ (D : TyP Ei n Γ e T) →
    {A body arg : Expr Nat}→ (he : e = .app (.lam A body) arg) → D.AssumpPref →
    (readRedex hext Aw D he).apBoth
  | _, _, _, _, .sort .., _, _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, _, he, _ => by cases he
  | _, _, _, _, .pi .., _, _, _, he, _ => by cases he
  | _, _, _, _, .lam .., _, _, _, he, _ => by cases he
  | _, _, _, _, .letE .., _, _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, _, he, _ => by cases he
  | _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _, _, _, _, he, hap => by
      cases he
      dsimp only [readRedex]
      have hapL : (readLam hext Aw hf rfl).apBody :=
        lamRead_ap hext Aw hf rfl hap.1
      cases hlr : readLam hext Aw hf rfl with
      | yes gl =>
          show (redexOfApp hext Aw gl ha _).hbody.AssumpPref ∧
            (redexOfApp hext Aw gl ha _).harg.AssumpPref
          refine redexOfApp_apBoth hext Aw gl ha _ ?_ hap.2.1
          have h3 : LamRead.apBody (LamRead.yes gl) := by rw [← hlr]; exact hapL
          exact h3
      | no => simp only [RedexRead.apBoth]
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner _, _, _, _, he, hap => by
      simp only [readRedex]
      rw [RedexRead.apBoth_raise]
      exact redexRead_ap hext Aw inner he hap.1
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, _, he, hap => by
      dsimp only [readRedex]
      cases lift_eq_app he with
      | mk _ _ he₀ hf₀ ha₀ =>
          cases lift_eq_lam hf₀ with
          | mk _ _ heLam hAe hb₀ =>
              show (RedexRead.raise _ (pushRedexWk d c
                (readRedex hext Aw inner (app_of_lam he₀ heLam)) hAe hb₀
                ha₀)).apBoth
              rw [RedexRead.apBoth_raise]
              exact pushRedexWk_apBoth d c _ hAe hb₀ ha₀ hap.1
                (redexRead_ap hext Aw inner (app_of_lam he₀ heLam) hap.2)
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, _, he, hap => by
      dsimp only [readRedex]
      cases instantiate_eq_app he with
      | under _ _ he₀ hf₀ ha₀ =>
          dsimp only
          split
          next =>
            exact pushRedexEsub_apBoth hext Aw hget hv hvT _ _ _ ha₀ _ _ _ _
              hap.1 (redexRead_ap hext Aw inner _ hap.2.1) hap.2.2.1 hap.2.2.2
          next => trivial
      | here _ hr =>
          show (RedexRead.raise _ (readRedex hext Aw hv hr)).apBoth
          rw [RedexRead.apBoth_raise]
          exact redexRead_ap hext Aw hv hr hap.2.2.1
  | _, _, _, _, .lsub .., _, _, _, _, _ => by
      simp only [readRedex, RedexRead.apBoth]
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, _, he, hap => by
      dsimp only [readRedex]
      cases instantiateLevels_eq_app he with
      | mk _ _ he₀ hf₀ ha₀ =>
          cases instantiateLevels_eq_lam hf₀ with
          | mk _ _ heLam hAe hb₀ =>
              show (RedexRead.raise _ (pushRedexLinst ls hls hlen
                (readRedex hext Aw inner (app_of_lam he₀ heLam)) hAe hb₀
                ha₀)).apBoth
              rw [RedexRead.apBoth_raise]
              exact pushRedexLinst_apBoth ls hls hlen _ hAe hb₀ ha₀
                (redexRead_ap hext Aw inner (app_of_lam he₀ heLam) hap)
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, _, he, hap => by
      simp only [readRedex]
      rw [RedexRead.apBoth_raise]
      exact redexRead_ap (envExt_trans hext' hext) Aw inner he hap
  | _, _, _, _, .cctx .., _, _, _, _, _ => by
      simp only [readRedex, RedexRead.apBoth]

/-- The closer-facing form: at `redexRead Aw D = .yes g`, `D.AssumpPref`
    gives both extracted typings' `AssumpPref` — the row-2 issuance row's
    AP side condition, exactly as the closer calls it. -/
theorem redexRead_ap_yes {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg T : Expr Nat} (Aw : Nat → Nat)
    (D : TyP E n Γ (.app (.lam A body) arg) T) (hap : D.AssumpPref)
    {g : RedexGot Aw (D.wt Aw) E n Γ A body arg}
    (h : redexRead Aw D = .yes g) :
    g.hbody.AssumpPref ∧ g.harg.AssumpPref := by
  have hb := redexRead_ap (envExt_refl E) Aw D rfl hap
  have h' : readRedex (envExt_refl E) Aw D rfl = .yes g := h
  rw [h'] at hb
  exact hb

end Rcic.Syn

#print axioms Rcic.Syn.LamRead.apBody
#print axioms Rcic.Syn.RedexRead.apBoth
#print axioms Rcic.Syn.LamRead.apBody_raise
#print axioms Rcic.Syn.RedexRead.apBoth_raise
#print axioms Rcic.Syn.assumptionPrefix_cons
#print axioms Rcic.Syn.pushLamWk_apBody
#print axioms Rcic.Syn.pushLamLinst_apBody
#print axioms Rcic.Syn.pushBodyEsub_ap
#print axioms Rcic.Syn.pushLamEsub_apBody
#print axioms Rcic.Syn.pushRedexWk_apBoth
#print axioms Rcic.Syn.pushRedexLinst_apBoth
#print axioms Rcic.Syn.pushRedexEsub_apBoth
#print axioms Rcic.Syn.redexOfApp_apBoth
#print axioms Rcic.Syn.lamRead_ap
#print axioms Rcic.Syn.redexRead_ap
#print axioms Rcic.Syn.redexRead_ap_yes
