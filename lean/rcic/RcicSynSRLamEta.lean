import rcic.RcicSynClosedEslam
import rcic.RcicSynClosedEta
import rcic.RcicSynTableOfIFull

/-!
# Syntactic sortRow, tableOfI closure — rows 9 (`es_lam`) and 12 (`es_eta`)

`sortrow` closure lane `sr-eta`. Census rows: `lam_got_*`/`lam_body_cl_*`/
`lam_bodyTag` (row 9) and `eta_appGot`/`eta_binder_cls` (row 12); `tableWF`
is discharged by `tableWF_tableOfI_full` (`swe-tableicompat`).

Measurement: the producers that feed `got` are the landed readers
`readLam`/`readApp`, and both decline `lsub` or `cctx`-headed derivations by
construction (`.no`). A wall-free `lam_got`/`eta_appGot` would need a body
decoder through `setAssump`-context conversion (`tyCctxAt`); its output is a
fresh re-derivation whose `TyP.atoms` do not admit a `dl.wt` bound, so the
`LamGot.lt`/`AppGot.ltF`/`ltA` fields cannot be produced compositionally.
The binder-display `CL`/`TagCoh` ports stay transport-sensitive walls.

§1 records the kernel-checked reader facts: `readLam`/`readApp` evaluate
to `.no` on concrete `cctx`-headed fixtures (`dl_cctx`, `dapp_cctx`) —
measurement evidence only, not refutations of closer-consumed lemmas.
§2 restates each row's exact remaining wall as ONE named `Type` at
`tableOfI hW`; §3 gives the conditional field theorems.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv}

/-! ## §1 kernel-checked reader facts (no row-status bearing)

    Concrete evidence for the measurement: `readLam`/`readApp` evaluate to
    `.no` on `cctx`-headed fixtures. These are facts about the readers,
    not refutations of any lemma the closers consume — the closers feed
    the verdict-matched residual (row 9) and the redex-instance ports
    (row 12), both restated verbatim in §2. -/

/-- `sort 0 : sort 1` two assumptions deep — fixture for `dl_ctx`. -/
def dS0_ctx2 : TyP emptyEnv 0 [.assumption EslamFix.S0, .assumption EslamFix.S0]
    EslamFix.S0 EslamFix.S1 :=
  TyP.sort emptyEnv 0 [.assumption EslamFix.S0, .assumption EslamFix.S0]
    .zero (.succ .zero) (eqN_refl _)

/-- `sort 1 : sort 2` two assumptions deep — fixture for `dl_ctx`. -/
def dS1_ctx2 : TyP emptyEnv 0 [.assumption EslamFix.S0, .assumption EslamFix.S0]
    EslamFix.S1 EslamFix.S2 :=
  TyP.sort emptyEnv 0 [.assumption EslamFix.S0, .assumption EslamFix.S0]
    (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- The canonical sort-lam inside one extra assumption — `cctx` input. -/
def dl_ctx : TyP emptyEnv 0 [.assumption EslamFix.S0]
    (.lam EslamFix.S0 EslamFix.S0) (.pi EslamFix.S0 EslamFix.S1) :=
  TyP.lam emptyEnv 0 [.assumption EslamFix.S0] EslamFix.S0 (.succ .zero)
    EslamFix.S0 EslamFix.S1 (.succ (.succ .zero))
    EslamFix.dS0_ctx dS0_ctx2 dS1_ctx2

/-- A `cctx`-headed lam-typing: `readLam` declines it by construction. -/
def dl_cctx : TyP emptyEnv 0 [.assumption EslamFix.S0]
    (.lam EslamFix.S0 EslamFix.S0) (.pi EslamFix.S0 EslamFix.S1) :=
  TyP.cctx emptyEnv 0 [] (.lam EslamFix.S0 EslamFix.S0)
    (.pi EslamFix.S0 EslamFix.S1) EslamFix.S0 EslamFix.S0 (.succ .zero)
    dl_ctx EslamFix.hA_can

/-- `readLam` evaluates to `.no` on the `cctx`-headed fixture — a fact
    about the reader (it declines `lsub`/`cctx` by construction), not a
    refutation of any lemma `es_lam_closed` consumes. -/
theorem readLam_cctx_no (Aw : Nat → Nat) :
    readLam (envExt_refl emptyEnv) Aw dl_cctx rfl = .no := rfl

/-- The eta-body application under one assumption — `cctx` input. -/
def dapp : TyP emptyEnv 0 [.assumption EslamFix.S0]
    (.app (lift 0 1 (.lam EslamFix.S0 EslamFix.S0)) (.bvar 0)) EslamFix.S1 :=
  TyP.app emptyEnv 0 [.assumption EslamFix.S0]
    (lift 0 1 (.lam EslamFix.S0 EslamFix.S0)) (.bvar 0)
    EslamFix.S0 EslamFix.S1 (.succ (.succ .zero))
    (TyP.wk emptyEnv 0 [] (.lam EslamFix.S0 EslamFix.S0)
      (.pi EslamFix.S0 EslamFix.S1) (.assumption EslamFix.S0) 0 EslamFix.dl_can)
    (TyP.bvar emptyEnv 0 [.assumption EslamFix.S0] 0 EslamFix.S0
      (.succ .zero) rfl EslamFix.dS0_ctx)
    EslamFix.dS1_ctx

/-- A `cctx`-headed app-typing: `readApp` declines it by construction. -/
def dapp_cctx : TyP emptyEnv 0 [.assumption EslamFix.S0]
    (.app (lift 0 1 (.lam EslamFix.S0 EslamFix.S0)) (.bvar 0)) EslamFix.S1 :=
  TyP.cctx emptyEnv 0 [] (.app (lift 0 1 (.lam EslamFix.S0 EslamFix.S0))
    (.bvar 0)) EslamFix.S1 EslamFix.S0 EslamFix.S0 (.succ .zero)
    dapp EslamFix.hA_can

/-- `readApp` evaluates to `.no` on the `cctx`-headed fixture — same
    reader fact (declines `lsub`/`cctx`); not a refutation of the
    `EtaResiduum.got` port `es_eta_closed` feeds. -/
theorem readApp_cctx_no (Aw : Nat → Nat) :
    readApp (envExt_refl emptyEnv) Aw (dapp_cctx.wt Aw + 1) dapp_cctx rfl
      (fun y hy => Nat.lt_succ_of_le (TyP.atoms_le Aw dapp_cctx y hy)) =
    .no := rfl

/-! ## §2 the exact restated walls at `tableOfI hW`, one named type each -/

/-- Row 9 (`es_lam`): the landed `LamFieldResidClosed` instance at
    `tbl := tableOfI hW`, verbatim — reader reads, verdict branches, and
    the binder-display body `CL`/`TagCoh` residuals unchanged. -/
def EsLamTableIWall (Aw : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {Eₐ : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type :=
  LamFieldResidClosed Aw (tableOfI hW) hA hb dl dr S σ ρ
    (readLam (envExt_refl E) Aw dl rfl)
    (epsReadLam (envExt_refl E) Aw σ dl rfl ρ)
    (readLam (envExt_refl E) Aw dr rfl)
    (epsReadLam (envExt_refl E) Aw σ dr rfl ρ)

/-- Row 12 (`es_eta`): `EtaResiduum` minus `tableWF` (discharged by
    `tableWF_tableOfI_full hW`) — `eta_appGot` and `eta_binder_cls`
    verbatim at `tbl := tableOfI hW`. -/
structure EsEtaTableIWall (Aw : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (σ : Level → Level) (ρ : List Disp) : Type where
  /-- `AppGot` of the eta body — `eta_appGot`, verbatim. -/
  got : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
  /-- `dl` erases to the η clause — verbatim. -/
  eps : dl.eps σ ρ =
      lamErasure (levelIsZero (σ (etaDom dl).u))
        (appClauseOf got σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ))
  /-- `CL[got.hf, wkAtZero hf]` at the binder display — `eta_binder_cls`,
      verbatim. -/
  funCl : CL (tableOfI hW) σ
      (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      got.hf (wkAtZero (A := A) hf)
  /-- `CL[got.ha, etaArg hA]` at the binder display — `eta_binder_cls`,
      verbatim. -/
  argCl : CL (tableOfI hW) σ
      (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      got.ha (etaArg (etaDom_hA dl))
  /-- `TagCoh[got.ha, etaArg hA]` at the binder display — `eta_binder_cls`,
      verbatim. -/
  argTag : TagCoh σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      got.ha (etaArg (etaDom_hA dl))

/-! ## §3 the conditional field theorems at `tableOfI hW` -/

/-- `StepSuppliers.es_lam` at `tbl := tableOfI hW`, conditional on the ONE
    named wall `EsLamTableIWall`. -/
theorem es_lam_tableI (Aw : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {Eₐ : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (wall : EsLamTableIWall Aw hW hA hb dl dr S σ ρ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) :=
  es_lam_closed Aw (tableOfI hW) hA hb dl dr S σ ρ wall

/-- `StepSuppliers.es_eta` at `tbl := tableOfI hW`, conditional on the ONE
    named wall `EsEtaTableIWall`; `tableWF` is supplied unconditionally. -/
theorem es_eta_tableI (Aw : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {Eₐ : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (wall : EsEtaTableIWall Aw hW hf dl σ ρ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) :=
  es_eta_closed Aw (tableOfI hW) hf dl dr S σ ρ
    { tableWF := tableWF_tableOfI_full hW
      got := wall.got
      eps := wall.eps
      funCl := wall.funCl
      argCl := wall.argCl
      argTag := wall.argTag }

/-! ## §4 accepted-axiom audit -/

#print axioms readLam_cctx_no
#print axioms readApp_cctx_no
#print axioms es_lam_tableI
#print axioms es_eta_tableI
