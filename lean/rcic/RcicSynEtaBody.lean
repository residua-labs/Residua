import rcic.RcicSynEtaLam

/-!
# Syntactic sortRow, build step 3ae — the stored η λ, read as the application

`research/rcic/semantic/S3_ES_ARMS.md` §30. `readLam` returns the body of a
typing of `.lam`. On `lam A (app (lift 0 1 f) (bvar 0))` that body is the
application `etaLam` is built from, and nothing in the reader said so.

`readApp` walks a typing of `.app f arg` and returns the function and the
argument. `cctx` and `lsub` stay `.no`, as they do for a λ and for a redex.
Every other constructor is pushed. The atom bound is not the derivation's
weight: it is a `src` every atom of the derivation already sits under, so a
`wk` whose weight exceeds `src` still returns children under `src`.
`meetEta` is `readLam`, then `readApp` on the body, at `src = D.wt`. The
extracted atoms sit under the stored λ.

`etaApp` is the application inside `etaLam`. Its erasure is `appClause` of
the weakened `f` and of `bvar 0`. On a relevant non-`★` domain that is the η
redex `es_eta` steps; on a proof domain it is `f`'s erasure. `readApp` on a
pure `app` is `.yes`, and the got's erasures are the two sides of that clause.

Not proved. The walk that sends an arbitrary body to `appClause` of the
extracted function and argument. `es_eta` on the stored `dl`. `wk` and `esub`
of a bvar, so the extracted argument is `bvar 0` beyond the pure node.
`delta`'s left constant, the right endpoints of `app` and `pi`, and
`zetaLocal` at an arbitrary `ρ`. The fix that builds `Below` is not this
module. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv}

/-! ## §1 an application, in two typings -/

structure AppGot (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (f arg : Expr Nat) : Type where
  A : Expr Nat
  B : Expr Nat
  hf : TyP E n Γ f (.pi A B)
  ha : TyP E n Γ arg A
  ltF : ∀ y ∈ hf.atoms Aw, y < src
  ltA : ∀ y ∈ ha.atoms Aw, y < src

inductive AppRead (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (f arg : Expr Nat) : Type where
  | yes (g : AppGot Aw src E n Γ f arg)
  | no

def AppRead.isYes {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f arg : Expr Nat} : AppRead Aw src E n Γ f arg → Bool
  | .yes _ => true
  | .no => false

def appOfNode {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) (src : Nat)
    {n : Nat} {Γ : LCtx} {f arg A B : Expr Nat} {w : Level}
    (hf : TyP Ei n Γ f (.pi A B)) (ha : TyP Ei n Γ arg A)
    (hT : TyP Ei n Γ (instantiate0 arg B) (.sort w))
    (hAt : ∀ y ∈ (TyP.app Ei n Γ f arg A B w hf ha hT).atoms Aw, y < src) :
    AppGot Aw src E n Γ f arg :=
  let D := TyP.app Ei n Γ f arg A B w hf ha hT
  let hw : D.wt Aw < src := hAt (D.wt Aw) (by
    simp only [TyP.atoms]
    exact List.mem_singleton.mpr rfl)
  let hfw : hf.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  let haw : ha.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  { A := A
    B := B
    hf := TyP.ewk Ei E n Γ f (.pi A B) hext hf
    ha := TyP.ewk Ei E n Γ arg A hext ha
    ltF := fun y hy => by
      rw [show (TyP.ewk Ei E n Γ f (.pi A B) hext hf).atoms Aw = hf.atoms Aw from rfl] at hy
      exact Nat.lt_trans (atoms_lt_of_wt_lt Aw hf hfw y hy) hw
    ltA := fun y hy => by
      rw [show (TyP.ewk Ei E n Γ arg A hext ha).atoms Aw = ha.atoms Aw from rfl] at hy
      exact Nat.lt_trans (atoms_lt_of_wt_lt Aw ha haw y hy) hw }

/-! ## §2 transports keep the external bound -/

def pushAppWk {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {f₀ arg₀ : Expr Nat} (d : LocalDecl) (c : Nat)
    (r : AppRead Aw src E n Γ₀ f₀ arg₀) {f arg : Expr Nat}
    (hf : lift c 1 f₀ = f) (ha : lift c 1 arg₀ = arg) :
    AppRead Aw src E n (insertAt d c Γ₀) f arg :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        A := lift c 1 g.A
        B := lift (c + 1) 1 g.B
        hf := tyCast hf rfl (TyP.wk E n Γ₀ f₀ (.pi g.A g.B) d c g.hf)
        ha := tyCast ha rfl (TyP.wk E n Γ₀ arg₀ g.A d c g.ha)
        ltF := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltF y hy
        ltA := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltA y hy }

def pushAppLinst {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ₀ : LCtx} {f₀ arg₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (r : AppRead Aw src E a Γ₀ f₀ arg₀) {f arg : Expr Nat}
    (hf : instantiateLevels ls f₀ = f) (ha : instantiateLevels ls arg₀ = arg) :
    AppRead Aw src E n (instLvlsCtx ls Γ₀) f arg :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        A := instantiateLevels ls g.A
        B := instantiateLevels ls g.B
        hf := tyCast hf rfl
          (TyP.linst E a n Γ₀ f₀ (.pi g.A g.B) ls hls hlen g.hf)
        ha := tyCast ha rfl
          (TyP.linst E a n Γ₀ arg₀ g.A ls hls hlen g.ha)
        ltF := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltF y hy
        ltA := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltA y hy }

def pushAppEsub {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {src : Nat} {n : Nat} {Γ₀ : LCtx} {f₀ arg₀ t repl : Expr Nat}
    {j : Nat} {uE : Level}
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (r : AppRead Aw src E n Γ₀ f₀ arg₀) {f arg : Expr Nat}
    (hfEq : instantiate j (lift 0 j repl) f₀ = f)
    (haEq : instantiate j (lift 0 j repl) arg₀ = arg)
    (hAtv : ∀ y ∈ hv.atoms Aw, y < src)
    (hAtT : ∀ y ∈ hvT.atoms Aw, y < src) :
    AppRead Aw src E n (substRemove repl j Γ₀) f arg :=
  match r with
  | .no => .no
  | .yes g =>
      let hvE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv
      let hvTE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT
      .yes {
        A := instantiate j (lift 0 j repl) g.A
        B := instantiate (j + 1) (lift 0 1 (lift 0 j repl)) g.B
        hf := tyCast hfEq rfl
          (TyP.esub E n Γ₀ f₀ (.pi g.A g.B) t repl j uE g.hf hget hvE hvTE)
        ha := tyCast haEq rfl
          (TyP.esub E n Γ₀ arg₀ g.A t repl j uE g.ha hget hvE hvTE)
        ltF := by
          intro y hy
          rw [atoms_tyCast, atoms_esub] at hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy
          cases List.mem_append.mp hy with
          | inl hy =>
            cases List.mem_append.mp hy with
            | inl hyf => exact g.ltF y hyf
            | inr hyv => exact hAtv y hyv
          | inr hyT => exact hAtT y hyT
        ltA := by
          intro y hy
          rw [atoms_tyCast, atoms_esub] at hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy
          cases List.mem_append.mp hy with
          | inl hy =>
            cases List.mem_append.mp hy with
            | inl hya => exact g.ltA y hya
            | inr hyv => exact hAtv y hyv
          | inr hyT => exact hAtT y hyT }

/-! ## §3 the atom bound, one constructor in -/

theorem wk_atom_src (Aw : Nat → Nat) {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl} {c : Nat}
    (inner : TyP E n Γ e A)
    (hAt : ∀ y ∈ (TyP.wk E n Γ e A d c inner).atoms Aw, y < src) :
    ∀ y ∈ inner.atoms Aw, y < src := by
  simpa [TyP.atoms] using hAt

theorem linst_atom_src (Aw : Nat → Nat) {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ : LCtx} {e A : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (inner : TyP E a Γ e A)
    (hAt : ∀ y ∈ (TyP.linst E a n Γ e A ls hls hlen inner).atoms Aw, y < src) :
    ∀ y ∈ inner.atoms Aw, y < src := by
  simpa [TyP.atoms] using hAt

theorem ewk_atom_src (Aw : Nat → Nat) {src : Nat} {E₀ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} (hext : EnvExt E₀ E) (inner : TyP E₀ n Γ e A)
    (hAt : ∀ y ∈ (TyP.ewk E₀ E n Γ e A hext inner).atoms Aw, y < src) :
    ∀ y ∈ inner.atoms Aw, y < src := by
  simpa [TyP.atoms] using hAt

theorem conv_atom_src (Aw : Nat → Nat) {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (inner : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (hAt : ∀ y ∈ (TyP.conv E n Γ e A B u inner hc).atoms Aw, y < src) :
    ∀ y ∈ inner.atoms Aw, y < src := by
  intro y hy
  have hw : (TyP.conv E n Γ e A B u inner hc).wt Aw < src :=
    hAt _ (by simp only [TyP.atoms]; exact List.mem_singleton.mpr rfl)
  have hi : inner.wt Aw < (TyP.conv E n Γ e A B u inner hc).wt Aw := by
    simp only [TyP.wt]; omega
  exact Nat.lt_trans (atoms_lt_of_wt_lt Aw inner hi y hy) hw

theorem esub_inner_src (Aw : Nat → Nat) {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (inner : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hAt : ∀ y ∈ (TyP.esub E n Γ e A t v j u inner hget hv hvT).atoms Aw, y < src) :
    ∀ y ∈ inner.atoms Aw, y < src := by
  intro y hy
  exact hAt y (by
    simp only [TyP.atoms]
    exact List.mem_append_left _ (List.mem_append_left _ hy))

theorem esub_val_src (Aw : Nat → Nat) {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (inner : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hAt : ∀ y ∈ (TyP.esub E n Γ e A t v j u inner hget hv hvT).atoms Aw, y < src) :
    ∀ y ∈ hv.atoms Aw, y < src := by
  intro y hy
  exact hAt y (by
    simp only [TyP.atoms]
    exact List.mem_append_left _ (List.mem_append_right _ hy))

theorem esub_ty_src (Aw : Nat → Nat) {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (inner : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hAt : ∀ y ∈ (TyP.esub E n Γ e A t v j u inner hget hv hvT).atoms Aw, y < src) :
    ∀ y ∈ hvT.atoms Aw, y < src := by
  intro y hy
  exact hAt y (by simp only [TyP.atoms]; exact List.mem_append_right _ hy)

/-! ## §4 the reader -/

set_option maxHeartbeats 800000 in
def readApp {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) (src : Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {f arg : Expr Nat} → (he : e = .app f arg) →
    (hAt : ∀ y ∈ D.atoms Aw, y < src) →
    AppRead Aw src E n Γ f arg
  | _, _, _, _, .sort .., _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _ => by cases he
  | _, _, _, _, .pi .., _, _, he, _ => by cases he
  | _, _, _, _, .lam .., _, _, he, _ => by cases he
  | _, _, _, _, .app _ _ _ f a A B w hf ha hT, _, _, he, hAt =>
      match f, a, he with
      | _, _, rfl => .yes (appOfNode hext Aw src hf ha hT hAt)
  | _, _, _, _, .letE .., _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, he, hAt =>
      readApp hext Aw src inner he (conv_atom_src Aw inner hc hAt)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, hAt =>
      match lift_eq_app he with
      | .mk f₀ arg₀ he₀ hf₀ ha₀ =>
          pushAppWk d c (readApp hext Aw src inner he₀ (wk_atom_src Aw inner hAt)) hf₀ ha₀
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, hAt =>
      match instantiate_eq_app he with
      | .under f₀ arg₀ he₀ hf₀ ha₀ =>
          pushAppEsub hext Aw hget hv hvT
            (readApp hext Aw src inner he₀
              (esub_inner_src Aw inner hget hv hvT hAt))
            hf₀ ha₀
            (esub_val_src Aw inner hget hv hvT hAt)
            (esub_ty_src Aw inner hget hv hvT hAt)
      | .here _ hr =>
          readApp hext Aw src hv hr (esub_val_src Aw inner hget hv hvT hAt)
  | _, _, _, _, .lsub .., _, _, _, _ => .no
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, hAt =>
      match instantiateLevels_eq_app he with
      | .mk f₀ arg₀ he₀ hf₀ ha₀ =>
          pushAppLinst ls hls hlen
            (readApp hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt))
            hf₀ ha₀
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, he, hAt =>
      readApp (envExt_trans hext' hext) Aw src inner he (ewk_atom_src Aw hext' inner hAt)
  | _, _, _, _, .cctx .., _, _, _, _ => .no

theorem readApp_app_yes (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {f arg A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ arg A)
    (hT : TyP E n Γ (instantiate0 arg B) (.sort w)) :
    (readApp (envExt_refl E) Aw ((TyP.app E n Γ f arg A B w hf ha hT).wt Aw + 1)
      (TyP.app E n Γ f arg A B w hf ha hT) rfl
      (fun y hy => atoms_lt_of_wt_lt Aw (TyP.app E n Γ f arg A B w hf ha hT)
        (Nat.lt_succ_self _) y hy)).isYes = true := by
  rfl

theorem readApp_app_hf_eps {Ei : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx}
    {f arg A B : Expr Nat} {w : Level}
    (hf : TyP Ei n Γ f (.pi A B)) (ha : TyP Ei n Γ arg A)
    (hT : TyP Ei n Γ (instantiate0 arg B) (.sort w))
    (hAt : ∀ y ∈ (TyP.app Ei n Γ f arg A B w hf ha hT).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp) :
    (match readApp hext Aw src (TyP.app Ei n Γ f arg A B w hf ha hT) rfl hAt with
      | .yes g => g.hf.eps σ ρ
      | .no => hf.eps σ ρ) = hf.eps σ ρ := by
  unfold readApp appOfNode
  rfl

theorem readApp_ewk_cast_yes (Aw : Nat → Nat) {src : Nat} {n : Nat} {Γ : LCtx}
    {f arg A B T₀ : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ arg A)
    (hT : TyP E n Γ (instantiate0 arg B) (.sort w))
    (hEq : instantiate0 arg B = T₀)
    (hAt : ∀ y ∈ (TyP.ewk E E n Γ (.app f arg) T₀ (envExt_refl E)
        (tyCast rfl hEq (TyP.app E n Γ f arg A B w hf ha hT))).atoms Aw, y < src) :
    (readApp (envExt_refl E) Aw src
      (TyP.ewk E E n Γ (.app f arg) T₀ (envExt_refl E)
        (tyCast rfl hEq (TyP.app E n Γ f arg A B w hf ha hT))) rfl hAt).isYes = true := by
  cases hEq
  unfold readApp
  unfold readApp
  rfl

theorem readApp_app_ha_eps {Ei : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx}
    {f arg A B : Expr Nat} {w : Level}
    (hf : TyP Ei n Γ f (.pi A B)) (ha : TyP Ei n Γ arg A)
    (hT : TyP Ei n Γ (instantiate0 arg B) (.sort w))
    (hAt : ∀ y ∈ (TyP.app Ei n Γ f arg A B w hf ha hT).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp) :
    (match readApp hext Aw src (TyP.app Ei n Γ f arg A B w hf ha hT) rfl hAt with
      | .yes g => g.ha.eps σ ρ
      | .no => ha.eps σ ρ) = ha.eps σ ρ := by
  unfold readApp appOfNode
  rfl

/-! ## §5 `readLam`, then the body -/

inductive EtaMeet (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A f : Expr Nat) : Type where
  | yes (g : AppGot Aw src E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
  | no

def EtaMeet.isYes {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A f : Expr Nat} : EtaMeet Aw src E n Γ A f → Bool
  | .yes _ => true
  | .no => false

theorem ofRead_isYes {Aw : Nat → Nat} {src : Nat} {n : Nat} {Γ : LCtx} {A f : Expr Nat}
    (r : AppRead Aw src E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)) :
    (match r with
      | .no => EtaMeet.no
      | .yes a => EtaMeet.yes a : EtaMeet Aw src E n Γ A f).isYes = r.isYes := by
  cases r <;> rfl

def meetEta {Ei : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {n : Nat} {Γ : LCtx} {e T A f : Expr Nat} (D : TyP Ei n Γ e T)
    (he : e = .lam A (.app (lift 0 1 f) (.bvar 0))) :
    EtaMeet Aw (D.wt Aw) E n Γ A f :=
  match readLam hext Aw D he with
  | .no => .no
  | .yes g =>
      match readApp (envExt_refl E) Aw (D.wt Aw) g.hbody rfl g.lt with
      | .no => .no
      | .yes a => .yes a

/-- A pure λ whose body is a pure application is `.yes`. The body `readLam`
    returns is that application, environment-weakened, and `readApp` reads it. -/
theorem meetEta_lam_app_yes (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {A f Ad Bd : Expr Nat} {u v w : Level}
    (hA : TyP E n Γ A (.sort u))
    (hf : TyP E n (.assumption A :: Γ) (lift 0 1 f) (.pi Ad Bd))
    (ha : TyP E n (.assumption A :: Γ) (.bvar 0) Ad)
    (hT : TyP E n (.assumption A :: Γ) (instantiate0 (.bvar 0) Bd) (.sort w))
    (hB : TyP E n (.assumption A :: Γ) (instantiate0 (.bvar 0) Bd) (.sort v)) :
    (meetEta (envExt_refl E) Aw
      (TyP.lam E n Γ A u (.app (lift 0 1 f) (.bvar 0))
        (instantiate0 (.bvar 0) Bd) v hA
        (TyP.app E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0) Ad Bd w hf ha hT)
        hB) rfl).isYes = true := by
  rfl

/-! ## §6 the pure application `etaLam` builds -/

def etaArg {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) :
    TyP E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A) :=
  TyP.bvar E n (.assumption A :: Γ) 0 (lift 0 1 A) u
    (lookup_assumption_zero A Γ) (wkAtZero (A := A) hA)

def etaApp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    TyP E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      (instantiate 0 (.bvar 0) (lift 1 1 B)) :=
  let hf := wkAtZero (A := A) h
  let ha := etaArg hA
  let hT := tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB
  TyP.app E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
    (lift 0 1 A) (lift 1 1 B) v hf ha hT

theorem etaLam_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    etaLam h hA hB =
      TyP.lam E n Γ A u (.app (lift 0 1 f) (.bvar 0)) B v hA
        (tyCast rfl (instantiate_bvar_lift_id 0 B) (etaApp h hA hB)) hB := by
  unfold etaLam etaApp etaArg
  rfl

theorem eta_fun_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} (h : TyP E n Γ f (.pi A B))
    (σ : Level → Level) (ρ : List Disp) :
    (wkAtZero (A := A) h).eps σ (.keep :: ρ) = (h.eps σ ρ).lift 0 1 := by
  rw [wkAtZero, eps_tyCastCtx, eps_wk_keep (hk := disp_keep_zero ρ), removeAt_zero,
    List.take_zero, countKeep]

theorem eta_fun_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} (h : TyP E n Γ f (.pi A B))
    (σ : Level → Level) (ρ : List Disp) :
    (wkAtZero (A := A) h).eps σ (.drop :: ρ) = h.eps σ ρ := by
  rw [wkAtZero, eps_tyCastCtx,
    eps_wk_not_keep (hk := Or.inr (Or.inl (disp_drop_zero ρ))), removeAt_zero]

theorem eta_arg_rel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false) :
    (etaArg hA).eps σ (.keep :: ρ) = .bvar 0 := by
  rw [etaArg, eps_bvar_rel hu, resolve_keep_zero]

theorem eta_arg_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true) :
    (etaArg hA).eps σ (.drop :: ρ) = .star := by
  rw [etaArg, eps_bvar_proof hu]

theorem etaApp_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (etaApp h hA hB).eps σ ρ =
      appClause ((wkAtZero (A := A) h).eps σ ρ) ((etaArg hA).eps σ ρ) := by
  simp only [etaApp, etaArg, eps_app_appClause]

theorem etaLam_eps_of_etaApp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (etaLam h hA hB).eps σ ρ =
      lamErasure (levelIsZero (σ u))
        ((etaApp h hA hB).eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) := by
  simp only [etaLam_expand, eps_lam_clause, eps_tyCast]

theorem readApp_etaApp_yes (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    (readApp (envExt_refl E) Aw ((etaApp h hA hB).wt Aw + 1) (etaApp h hA hB) rfl
      (fun y hy => atoms_lt_of_wt_lt Aw (etaApp h hA hB) (Nat.lt_succ_self _) y hy)).isYes
      = true := by
  unfold etaApp etaArg
  rfl

/-- `readLam` on `etaLam` meets `readApp` on `etaApp`. The cast is the
    codomain equation `instantiate_bvar_lift_id`; after it, both readers see
    the application. -/
theorem meetEta_etaLam_yes (Aw : Nat → Nat) {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    (meetEta (envExt_refl E) Aw (etaLam h hA hB) rfl).isYes = true := by
  rw [etaLam_expand]
  dsimp only [meetEta, readLam]
  split
  · rename_i _ heq
    unfold etaApp etaArg at heq
    have hnot := congrArg AppRead.isYes heq
    simp only [AppRead.isYes] at hnot
    dsimp only [EtaMeet.isYes]
    rw [← hnot]
    exact readApp_ewk_cast_yes Aw (wkAtZero (A := A) h)
      (TyP.bvar E n (.assumption A :: Γ) 0 (lift 0 1 A) u
        (lookup_assumption_zero A Γ) (wkAtZero (A := A) hA))
      (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB)
      (instantiate_bvar_lift_id 0 B) _
  · rfl

theorem etaLam_meets_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true) :
    (etaLam h hA hB).eps σ ρ = h.eps σ ρ := by
  rw [etaLam_eps_of_etaApp, etaApp_clause, hu, binderDisp_drop, eta_fun_drop,
    eta_arg_drop hA _ _ hu, appClause_right_star]
  rfl

theorem etaLam_meets_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false)
    (hn : h.eps σ ρ ≠ .star) :
    (etaLam h hA hB).eps σ ρ =
      .lam (.app ((h.eps σ ρ).lift 0 1) (.bvar 0)) := by
  rw [etaLam_eps_of_etaApp, etaApp_clause, hu, binderDisp_keep, eta_fun_keep,
    eta_arg_rel hA _ _ hu]
  rw [appClause_app (lift_ne_star hn) (by rintro ⟨⟩), lamErasure, lamClause_of_ne (by rintro ⟨⟩)]

theorem etaLam_meets_keep_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false)
    (hs : h.eps σ ρ = .star) :
    (etaLam h hA hB).eps σ ρ = .star := by
  rw [etaLam_eps_of_etaApp, etaApp_clause, hu, binderDisp_keep, eta_fun_keep, hs]
  rfl

end Rcic.Syn

#print axioms Rcic.Syn.readApp
#print axioms Rcic.Syn.meetEta
#print axioms Rcic.Syn.etaArg
#print axioms Rcic.Syn.etaApp
#print axioms Rcic.Syn.wk_atom_src
#print axioms Rcic.Syn.linst_atom_src
#print axioms Rcic.Syn.ewk_atom_src
#print axioms Rcic.Syn.conv_atom_src
#print axioms Rcic.Syn.esub_inner_src
#print axioms Rcic.Syn.esub_val_src
#print axioms Rcic.Syn.esub_ty_src
#print axioms Rcic.Syn.readApp_ewk_cast_yes
#print axioms Rcic.Syn.ofRead_isYes
#print axioms Rcic.Syn.readApp_app_yes
#print axioms Rcic.Syn.readApp_app_hf_eps
#print axioms Rcic.Syn.readApp_app_ha_eps
#print axioms Rcic.Syn.meetEta_lam_app_yes
#print axioms Rcic.Syn.etaLam_expand
#print axioms Rcic.Syn.eta_fun_keep
#print axioms Rcic.Syn.eta_fun_drop
#print axioms Rcic.Syn.eta_arg_rel
#print axioms Rcic.Syn.eta_arg_drop
#print axioms Rcic.Syn.etaApp_clause
#print axioms Rcic.Syn.etaLam_eps_of_etaApp
#print axioms Rcic.Syn.readApp_etaApp_yes
#print axioms Rcic.Syn.meetEta_etaLam_yes
#print axioms Rcic.Syn.etaLam_meets_drop
#print axioms Rcic.Syn.etaLam_meets_keep
#print axioms Rcic.Syn.etaLam_meets_keep_star
