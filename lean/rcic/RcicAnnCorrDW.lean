import rcic.RcicAnnIotaCorrW
import rcic.RcicIARecIH
import rcic.RcicTypedLevels
import rcic.RcicIotaFunRecWalk

/-!
# S7-1 — the generic `.annDW` discharge: gated certificate + recognizer-side legs

S0 (`research/rcic/corr/S0_GENERIC_DW.md`, draft #6733, posted on #6358): the
plain universal `∀ E, EnvWfT E → EnvCorrAnnDW E` is refutable —

- `drecFieldCheck` maps `.recursive (k+1)` fields to `directFragOne`, whose
  no-inner-escape clause is structurally false at a frec field (the S6 gate,
  by design).

The second claimed obstruction — sequential `instantiate0` corrupting open
args at `np ≥ 2` — was REFUTED by the #6733 ruling's own measurement
(`§(0)` below): at `qEnv`/`wOpen` the kernel-side `rhsArgsS` reduct and the
schema-side `iotaRhsOfS` agree on an open-major redex, `applyTel` and
`instPrefix` agree on open params, and the W-arm accepts.

The honest target is therefore the gated certificate `EnvCorrAnnDWC` here:
the per-witness `NoFunShapes` premise alone, matching the `EnvNoFunA`-gated
shape IA-024/DT-019's typed-side supply already carries.

## Contents (the legs needing no σ-correspondence — glm 3b-2b boundary in S0)

- §(0) `qEnv`/`wOpen` — the #6733 ruling's np ≥ 2 open-redex measurement.
- `ArgsClosed` (measured unnecessary), `NoFunShapes`, `EnvCorrAnnDWC`.
- C1: `drecFieldCheck`/`drecFragCheck` are `true` under `NoFunShapes` (the
  `… || true` arm; no fragment bridge needed).
- C2: `applyTel_some_of_piCount_le` — `args.length ≤ piCount T` ⇒ success;
  per-witness `applyTel` then exists by `hnpar`. `piCount` is unchanged by
  `instantiateLevels` via the sealed `piCount_instantiateLevels`.
  `applyTel_instPrefix_rest` is that success as `instPrefix`, with the
  leftover binders named by `(List.range m).map Expr.bvar`, and with no
  `exprClosedAt` premise (the premise glm's `tel_cons` uses, which #6733
  dropped). `applyTel_ctorAfter_fieldTel` is that image at a witness:
  `instPrefix` of `instantiateLevels` on `ctorFieldTelRaw`.
- C3 (stored telescope): a `.recursive 0` `fieldAnalyze` verdict makes
  `whnfFuel` at that same fuel const-headed, so `fieldsTelS` accepts
  `telWhnfDom` of `ctorFieldTelRaw` under `NoFunShapes`. The whnf'd
  `fieldsTelS` leg on `telWhnfDom` of `ctorAfter` is still the walk.
- C4+C5b: `instPrefix_minor_marker` — the canonical minor bvar
  `fl + ni + (nM-1-ctorIdx)` instantiates to `preMajor[np+1+ctorIdx]`.
- C5a: `iotaRhsOfS_eq_fold` — `iotaRhsOfS w` factors as
  `foldApps m (args.map (instPrefix _ ∘ instantiateLevels _))` whenever
  `hschema`'s `iotaArgs` returned `args`, using the sealed
  `foldApps_instantiateLevels`. The residual is the per-arg walk
  agreement (C5d — glm's 3b-2b core, `RcicIotaFunRecWalk` on
  `glm/nofunrec-s6`; not re-derived here).
- C5c: the sealed `instPrefix_instLs` — unconditional
  `instantiateLevels`/`instPrefix` commutation. No second induction.
- Assembly: `ctorAfterFieldTel` names that `applyTel` image. Under
  `NoFunShapes`, `iotaWitnessSAnnDW` reduces to `fieldsTelS` and `rhsEq`
  at `telWhnfDom` of the image. Those two stay the walk. `EnvWfT` is
  not read.

`closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) the #6733 ruling's measurement: np ≥ 2, open-major redex

cc's ruling (draft #6733): before `exprClosedAt 0` becomes a premise, settle
whether the sequential `instantiate0` walk corrupts **open** arguments on the
KERNEL's own reduct — `iotaReductA`'s `rhsArgsA`, which erases to `rhsArgsS`
(`rhsArgsA_erase`, RcicAnnTel).  `qEnv` below is the smallest such env:
`np = 2`, one index, one `.recursive 0` field whose `familyIdx` retains an
index mentioning parameter `P` — the `piEnv` class pushed across `np ≥ 2`.
`wOpen` puts the redex under a binder: `preMajor[0] = .bvar 0`,
`fields[0] = .bvar 0` are open terms (the recognizer is syntax-directed;
`IotaWitnessS` carries no closedness field, which is exactly what makes the
measurement possible without `EnvWfT`-level typing work).

Measured: `iotaRhsOfS` (canonical + `instPrefix`) vs `rhsArgsS` (real args +
sequential `instantiate0`) — the recognizer's own `rhsEq`, which is the kernel
reduct through erasure. -/

/-- `N : Sort 1`, `g : Π (_ : Sort 1), N` — the `piEnv` axiom pair. -/
def qAxNMember : CheckedMember := ⟨.axiomM, 0, .sort (.succ .zero), none⟩
def qAxGMember : CheckedMember :=
  ⟨.axiomM, 0, .pi (.sort (.succ .zero)) (.const 0 []), none⟩

/-- `I3 P Q i`. -/
def i3App (p q i : Nat) : Expr Nat :=
  .app (.app (.app (.const 2 []) (.bvar p)) (.bvar q)) (.bvar i)

/-- `g (bvar k)`. -/
def gApp' (k : Nat) : Expr Nat := .app (.const 1 []) (.bvar k)

/-- `I3 P Q (g (bvar k))`. -/
def i3AppG (p q k : Nat) : Expr Nat :=
  .app (.app (.app (.const 2 []) (.bvar p)) (.bvar q)) (gApp' k)

/-- `I3 : Π (P Q : Sort 1) (i : N), Sort 1` — `np = 2`, `ni = 1`. -/
def qFamType : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.sort (.succ .zero))
      (.pi (.const 0 []) (.sort (.succ .zero))))

/-- `mk : Π (P Q : Sort 1) (a : I3 P Q (g P)), I3 P Q (g P)` — the field's index
    mentions the NON-last parameter `P`. -/
def qMkType : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.sort (.succ .zero))
      (.pi (i3AppG 1 0 1) (i3AppG 2 1 2)))

/-- the derived minor:
    `Π (a : I3 P Q (g P)) (ih : M (g P) a), M (g P) (mk P Q a)`. -/
def qMinorTy : Expr Nat :=
  .pi (i3AppG 2 1 2)
    (.pi (.app (.app (.bvar 1) (gApp' 3)) (.bvar 0))
      (.app (.app (.bvar 2) (gApp' 4))
        (.app (.app (.app (.const 3 []) (.bvar 4)) (.bvar 3)) (.bvar 1))))

/-- `I3.rec : Π (P Q) (M : Π (i : N) (x : I3 P Q i), Sort p₀)
    (m : Π (a : I3 P Q (g P)) (ih : M (g P) a), M (g P) (mk P Q a))
    (i : N) (x : I3 P Q i), M i x` — the canonical recursor type at
    `np = 2`, `ni = 1`, `nM = 1`. -/
def qRecType : Expr Nat :=
  .pi (.sort (.succ .zero))
   (.pi (.sort (.succ .zero))
    (.pi (.pi (.const 0 [])
          (.pi (i3App 2 1 0) (.sort (.param 0))))
     (.pi qMinorTy
       (.pi (.const 0 [])
        (.pi (i3App 4 3 0)
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))

def qFamMember : CheckedMember := ⟨.inductiveM, 0, qFamType, none⟩
def qMkMember  : CheckedMember := ⟨.constructorM, 0, qMkType, none⟩
def qRecMember : CheckedMember := ⟨.recursorM, 1, qRecType, none⟩

def qB0 : ResolvedEnv := extendEnv emptyEnv 0 qAxNMember
def qB1 : ResolvedEnv := extendEnv qB0 1 qAxGMember
def qFamEnv : ResolvedEnv := extendEnv qB1 2 qFamMember
def qMkEnv : ResolvedEnv := extendEnv qFamEnv 3 qMkMember
def qEnv : ResolvedEnv := extendEnv qMkEnv 4 qRecMember

/-- the field is `.recursive 0`, and `familyIdx` keeps `g P` — the index of the
    NON-last parameter. -/
theorem q_fieldAnalyze :
    fieldAnalyze qFamEnv 8 2 0 2 1 2 (i3AppG 1 0 1) =
      .permitted (.recursive 0) [gApp' 1] := rfl

/-- the canonical schema `m a (I3.rec P Q M m (g P) a)` in the canonical
    equation context `(P Q M m i a)` — bvar 5 = P, bvar 4 = Q, bvar 3 = M,
    bvar 2 = m, bvar 1 = i, bvar 0 = a. -/
def qSchemaCorrect : Expr Nat :=
  .app (.app (.bvar 2) (.bvar 0))
    (.app (.app (.app (.app (.app (.app (.const 4 [.param 0])
        (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2))
        (.app (.const 1 []) (.bvar 5))) (.bvar 0))

/-- the OPEN-major witness at `qEnv`: the redex sits under a binder —
    `P' = .bvar 0`, `f' = .bvar 0`, `i' = g (.bvar 0)` are open; `Q'`, `M'`,
    `m'` are closed constants. -/
def wOpen : IotaWitnessS qEnv where
  recRef := 4
  ctorRef := 3
  ls := [.param 0]
  lsC := []
  recMember := qRecMember
  ctorMember := qMkMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 0, .const 9 [], .const 6 [], .const 7 [],
    .app (.const 1 []) (.bvar 0)]
  fields := [.bvar 0]
  ctorParams := [.bvar 0, .const 9 []]
  familyRef := 2
  famMember := qFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.sort (.succ .zero), .sort (.succ .zero), i3AppG 1 0 1]
  ctorResult := i3AppG 2 1 2
  hpeel := rfl
  hfamApp := rfl
  recDoms := [.sort (.succ .zero), .sort (.succ .zero),
    .pi (.const 0 []) (.pi (i3App 2 1 0) (.sort (.param 0))),
    qMinorTy, .const 0 [], i3App 4 3 0]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.recursive 0]
  hshapes := rfl
  schema := qSchemaCorrect
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : qEnv.members 0 = some qAxNMember := rfl
    have hmem1 : qEnv.members 1 = some qAxGMember := rfl
    have hmem2 : qEnv.members 2 = some qFamMember := rfl
    show iotaWitnessStableB qEnv 8
      [i3AppG 1 0 1] (fieldBvars 1)
      (lift 0 4 (ctorFieldTelRaw 2
        [.sort (.succ .zero), .sort (.succ .zero), i3AppG 1 0 1]
        (i3AppG 2 1 2))) = true
    simp [iotaWitnessStableB, i3AppG, gApp', fieldBvars, ctorFieldTelRaw,
      lift, constsMemberFuel, hmem0, hmem1, hmem2, qAxNMember, qAxGMember,
      qFamMember, transparent, instantiateLevels])
  hschemaScope := rfl

/-- the schema-side reduct: `instPrefix` restores every open arg verbatim —
    `P' = .bvar 0` lands back as `.bvar 0`, the recursive call's index is
    `g (.bvar 0)`. -/
theorem wOpenRhs_schema :
    iotaRhsOfS wOpen =
      .app (.app (.const 7 []) (.bvar 0))
        (.app (.app (.app (.app (.app (.app (.const 4 [.param 0])
            (.bvar 0)) (.const 9 [])) (.const 6 [])) (.const 7 []))
            (.app (.const 1 []) (.bvar 0))) (.bvar 0)) := by
  decide

/-- the kernel-side reduct (`rhsArgsS` on the real open args — `rhsArgsA`'s
    erasure): the SAME term — the sequential `instantiate0` walk does NOT
    corrupt the open `P'`/`f'` at `np = 2`. -/
theorem wOpenRhs_kernel :
    (match applyTel [.bvar 0, .const 9 []]
        (instantiateLevels [.param 0] qMkType) with
      | some ctorAfter =>
          foldApps (.const 7 [])
            (rhsArgsS (.const 4 [.param 0]) wOpen.preMajor 2 1 wOpen.fields
              [.recursive 0] (telWhnfDom qEnv 8 ctorAfter))
      | none => .lit 0) =
      .app (.app (.const 7 []) (.bvar 0))
        (.app (.app (.app (.app (.app (.app (.const 4 [.param 0])
            (.bvar 0)) (.const 9 [])) (.const 6 [])) (.const 7 []))
            (.app (.const 1 []) (.bvar 0))) (.bvar 0)) := by
  decide

/-- THE VERDICT: the W-arm accepts the open-major `np = 2` redex — kernel and
    schema reducts agree, so the sequential walk shows no corruption on this
    class.  The `exprClosedAt 0` premise is measured unnecessary HERE; the
    remaining gate is the frec exclusion alone. -/
theorem pin_iotaWitnessSAnnDArmW_wOpen :
    iotaWitnessSAnnDArmW qEnv wOpen = true := by
  decide

/-- the claimed `applyTel`-vs-`instPrefix` divergence, tested directly at
    `np = 2` with open args: the sequential walk and the parallel prefix
    produce the SAME instantiated telescope — `P' = .bvar 0` survives both. -/
theorem applyTel_instPrefix_open :
    applyTel [.bvar 0, .const 9 []] qMkType =
      some (instPrefix [.bvar 0, .const 9 []]
        (ctorFieldTelRaw 2
          [.sort (.succ .zero), .sort (.succ .zero), i3AppG 1 0 1]
          (i3AppG 2 1 2))) := by
  decide

/-! ## (1) the gated certificate -/

/-- The redex arguments are closed: every `bvar` inside them is bound.
    **Measured unnecessary** (`§(0)`): the `wOpen` probe shows sequential
    `instantiate0` and parallel `instPrefix` agree on open args at `np ≥ 2` —
    a placed arg's free refs sit strictly above the next instantiation index,
    so they are only decremented, never replaced.  Retained for the glm 3b-2b
    boundary in case their invariant surfaces a divergence this measurement
    did not reach. -/
def ArgsClosed (xs : List (Expr Nat)) : Prop :=
  ∀ e ∈ xs, exprClosedAt 0 e = true

/-- The witness's field shapes carry no function-recursive field — the
    noFun leg.  `.recursive 0` and `.nonrecursive` are admitted. -/
def NoFunShapes (shapes : List FieldShape) : Prop :=
  ∀ s ∈ shapes, ∀ k, s ≠ .recursive (k + 1)

/-- THE GATED per-env W certificate: every shape-based witness whose shapes
    are frec-free passes the DW-union recognizer.  (The ungated `EnvCorrAnnDW`
    is refuted exactly at frec fields — S0 §1(a); the open-arg obstruction
    of S0 §1(b) was refuted empirically by `pin_iotaWitnessSAnnDArmW_wOpen`.) -/
def EnvCorrAnnDWC (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E,
    NoFunShapes w.shapes →
    iotaWitnessSAnnDW E w = true

/-! ## (2) C1 — `drecFragCheck` is vacuous under `NoFunShapes` -/

/-- At a non-frec shape the δ-permissive field check hits its `… || true`
    arm — the direct fragment is not consulted. -/
theorem drecFieldCheck_of_noFun {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {s : FieldShape} (h : ∀ k, s ≠ .recursive (k + 1)) :
    drecFieldCheck E fuel fam nuniv nparams nindices depth T s = true := by
  cases s with
  | nonrecursive => exact Bool.or_true _
  | recursive j =>
      cases j with
      | zero => exact Bool.or_true _
      | succ k => exact absurd rfl (h k)

/-- The paired check is `true` at equal-length lists of non-frec shapes. -/
theorem drecFragCheck_of_noFun {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat}
    {doms : List (Expr Nat)} {shapes : List FieldShape}
    (hlen : doms.length = shapes.length) (hNF : NoFunShapes shapes) :
    drecFragCheck E fuel fam nuniv nparams nindices depth doms shapes = true := by
  induction doms generalizing shapes depth with
  | nil =>
      cases shapes with
      | nil => rfl
      | cons _ ss =>
          rw [List.length_nil, List.length_cons] at hlen
          exact absurd hlen.symm (Nat.succ_ne_zero ss.length)
  | cons T Ts ih =>
      cases shapes with
      | nil =>
          rw [List.length_cons, List.length_nil] at hlen
          exact absurd hlen (Nat.succ_ne_zero Ts.length)
      | cons s ss =>
          have hlen' : Ts.length = ss.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ.inj hlen
          simp only [drecFragCheck, Bool.and_eq_true]
          exact ⟨drecFieldCheck_of_noFun (hNF s (List.mem_cons_self s ss)),
            ih hlen' (fun s' hs' => hNF s' (List.mem_cons_of_mem s hs'))⟩

/-! ## (3) C2 — `applyTel` exists below the Π-count -/

/-- `instantiate` does not shrink the leading Π-count: a non-Π head stays at
    count 0, and a Π head recurses under the shifted index. -/
theorem piCount_le_instantiate (i : Nat) (a : Expr Nat) :
    ∀ (T : Expr Nat), piCount T ≤ piCount (instantiate i a T) := by
  intro T
  induction T generalizing i a with
  | pi _ B _ ihB =>
      simp only [instantiate, piCount]
      exact Nat.succ_le_succ (ihB (i + 1) (lift 0 1 a))
  | bvar _ =>
      simp only [piCount]
      exact Nat.zero_le _
  | sort _ =>
      simp only [piCount]
      exact Nat.zero_le _
  | const _ _ =>
      simp only [piCount]
      exact Nat.zero_le _
  | app _ _ _ _ =>
      simp only [piCount]
      exact Nat.zero_le _
  | lam _ _ _ _ =>
      simp only [piCount]
      exact Nat.zero_le _
  | letE _ _ _ _ _ _ =>
      simp only [piCount]
      exact Nat.zero_le _
  | lit _ =>
      simp only [piCount]
      exact Nat.zero_le _

theorem piCount_le_instantiate0 (a : Expr Nat) (T : Expr Nat) :
    piCount T ≤ piCount (instantiate0 a T) :=
  piCount_le_instantiate 0 a T

/-- A positive argument list cannot fit under a zero Π-count. -/
private theorem not_args_le_piCount_zero {a : Expr Nat} {as : List (Expr Nat)}
    {T : Expr Nat} (h : (a :: as).length ≤ piCount T) (h0 : piCount T = 0) :
    False := by
  rw [h0, List.length_cons] at h
  exact Nat.not_succ_le_zero as.length h

theorem applyTel_some_of_piCount_le {args : List (Expr Nat)} {T : Expr Nat}
    (h : args.length ≤ piCount T) :
    ∃ T', applyTel args T = some T' := by
  induction args generalizing T with
  | nil => exact ⟨T, rfl⟩
  | cons a as ih =>
      cases T with
      | pi A B =>
          rw [applyTel_cons_pi]
          apply ih
          -- `piCount (.pi A B)` and `(a :: as).length` reduce, so `h`
          -- is `as.length.succ ≤ (piCount B).succ`.
          exact Nat.le_trans (Nat.le_of_succ_le_succ h)
            (piCount_le_instantiate0 a B)
      | bvar _ => exact False.elim (not_args_le_piCount_zero h rfl)
      | sort _ => exact False.elim (not_args_le_piCount_zero h rfl)
      | const _ _ => exact False.elim (not_args_le_piCount_zero h rfl)
      | app _ _ => exact False.elim (not_args_le_piCount_zero h rfl)
      | lam _ _ => exact False.elim (not_args_le_piCount_zero h rfl)
      | letE _ _ _ => exact False.elim (not_args_le_piCount_zero h rfl)
      | lit _ => exact False.elim (not_args_le_piCount_zero h rfl)

/-- Per-witness: the parameter prefix applies to the stored constructor type
    (`hnpar`: `nparams + fields.length = piCount ctorMember.mtype`). -/
theorem applyTel_ctorParams {E : ResolvedEnv} (w : IotaWitnessS E) :
    ∃ T', applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
          some T' := by
  apply applyTel_some_of_piCount_le
  rw [List.length_take, piCount_instantiateLevels]
  have := w.hnpar
  omega

/-! ## (3a) C2 at `ctorAfter` — `applyTel` is `instPrefix`, with no closedness

glm's `tel_cons` (on `glm/nofunrec-s6`, not imported) states this bridge under
`exprClosedAt 0` of the telescope and of every argument. #6733 dropped that
premise: a placed argument is lifted past the binders still to be consumed, so
later `instantiate` steps only decrement it. `instPrefix_lift` cancels any
suffix of that length on a lifted term, and `instDoms` keeps the lifts. The
whnf'd `fieldsTelS` leg on this image is still the walk, not this lemma. -/

private def instDoms (j : Nat) (v : Expr Nat) : List (Expr Nat) → List (Expr Nat)
  | [] => []
  | E :: es => instantiate j v E :: instDoms (j + 1) (lift 0 1 v) es

private theorem peelPis_rebuild :
    (n : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) → T = ds.foldr Expr.pi r
  | 0, _, _, _, h => by
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds htr
      subst hds; subst htr
      rfl
  | n + 1, _, _, _, h => by
      have ⟨A, B, ds', hT, hds, hpeel⟩ := peelPis_succ h
      subst hT; subst hds
      simp only [List.foldr_cons]
      exact congrArg (Expr.pi A) (peelPis_rebuild n B hpeel)

private theorem instDoms_drop (j : Nat) (v : Expr Nat) :
    (l₁ l₂ : List (Expr Nat)) →
      (instDoms j v (l₁ ++ l₂)).drop l₁.length =
        instDoms (j + l₁.length) (lift 0 l₁.length v) l₂
  | [], _ => by
      simp only [List.nil_append, List.drop_zero, List.length_nil, Nat.add_zero,
        lift_zero]
  | E :: l₁, l₂ =>
      calc
        (instDoms j v ((E :: l₁) ++ l₂)).drop (E :: l₁).length
            = (instDoms (j + 1) (lift 0 1 v) (l₁ ++ l₂)).drop l₁.length := by
              simp only [List.cons_append, instDoms, List.length_cons,
                List.drop_succ_cons]
              rfl
          _ = instDoms ((j + 1) + l₁.length) (lift 0 l₁.length (lift 0 1 v)) l₂ :=
              instDoms_drop (j + 1) (lift 0 1 v) l₁ l₂
          _ = instDoms (j + (l₁.length + 1)) (lift 0 (l₁.length + 1) v) l₂ := by
              have hl : lift 0 l₁.length (lift 0 1 v) = lift 0 (l₁.length + 1) v := by
                have hm := lift_lift_merge l₁.length 1 0 0 (Nat.le_refl 0)
                  (by omega) v
                simpa [Nat.add_comm 1 l₁.length] using hm
              have hj : (j + 1) + l₁.length = j + (l₁.length + 1) := by omega
              rw [hl, hj]

private theorem peelPis_instantiate_doms :
    (n j : Nat) → (v e : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n e = some (ds, r) →
    peelPis n (instantiate j v e) =
      some (instDoms j v ds, instantiate (j + n) (lift 0 n v) r)
  | 0, _, _, _, _, _, h => by
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds htr
      subst hds; subst htr
      simp only [peelPis, instDoms, Nat.add_zero, lift_zero]
  | n + 1, j, v, _, _, _, h => by
      have ⟨_, B, _, hE, hds, hpeel⟩ := peelPis_succ h
      subst hE; subst hds
      have hinner := peelPis_instantiate_doms n (j + 1) (lift 0 1 v) B hpeel
      simp only [instantiate, peelPis, instDoms, hinner]
      have hidx : j + 1 + n = j + (n + 1) := by omega
      have hlift : lift 0 n (lift 0 1 v) = lift 0 (n + 1) v := by
        have hm := lift_lift_merge n 1 0 0 (Nat.le_refl 0) (by omega) v
        simpa [Nat.add_comm 1 n] using hm
      rw [hidx, hlift]

private theorem instantiate_foldr_pi (j : Nat) (v : Expr Nat) :
    (es : List (Expr Nat)) → (r : Expr Nat) →
    instantiate j v (es.foldr Expr.pi r) =
      (instDoms j v es).foldr Expr.pi
        (instantiate (j + es.length) (lift 0 es.length v) r)
  | [], _ => by
      simp only [List.foldr_nil, instDoms, List.length_nil, Nat.add_zero, lift_zero]
  | _ :: es, r => by
      simp only [List.foldr_cons, instantiate, instDoms, List.length_cons]
      rw [instantiate_foldr_pi (j + 1) (lift 0 1 v) es r]
      have hidx : j + 1 + es.length = j + (es.length + 1) := by omega
      have hlift : lift 0 es.length (lift 0 1 v) = lift 0 (es.length + 1) v := by
        have hm := lift_lift_merge es.length 1 0 0 (Nat.zero_le _) (by omega) v
        simpa [Nat.add_comm 1 es.length] using hm
      rw [hidx, hlift]

/-- C2 on a leftover telescope: applying `as` yields `instPrefix` of the
remaining `m` binders, named by `(List.range m).map Expr.bvar`. No
`exprClosedAt` premise. -/
theorem applyTel_instPrefix_rest
    (as : List (Expr Nat)) (m : Nat) (T : Expr Nat)
    {ds : List (Expr Nat)} {r : Expr Nat}
    (h : peelPis (as.length + m) T = some (ds, r)) :
    applyTel as T =
      some (instPrefix (as ++ (List.range m).map Expr.bvar)
        (lift 0 m ((ds.drop as.length).foldr Expr.pi r))) := by
  induction as generalizing T ds r with
  | nil =>
      rw [List.length_nil, Nat.zero_add] at h
      rw [List.nil_append, List.length_nil, List.drop_zero]
      rw [applyTel_nil]
      have hT := peelPis_rebuild m T h
      have hlen : ((List.range m).map (Expr.bvar : Nat → Expr Nat)).length = m := by
        rw [List.length_map, List.length_range]
      have hlift :=
        instPrefix_lift ((List.range m).map Expr.bvar) (ds.foldr Expr.pi r)
      rw [hlen] at hlift
      rw [hT]
      exact congrArg some hlift.symm
  | cons a as ih =>
      have hidx : as.length + 1 + m = as.length + m + 1 := by omega
      rw [List.length_cons, hidx] at h
      have ⟨_, B, ds', hT, hds, hpeel⟩ := peelPis_succ (n := as.length + m) h
      subst hT; subst hds
      have hpeelI := peelPis_instantiate_doms (as.length + m) 0 a B hpeel
      have hrec := ih (instantiate0 a B)
        (by simpa [instantiate0, Nat.zero_add] using hpeelI)
      rw [applyTel_cons_pi, hrec]
      apply congrArg some
      rw [List.cons_append, instPrefix_cons]
      apply congrArg (instPrefix (as ++ (List.range m).map Expr.bvar))
      have hlen : (as ++ (List.range m).map Expr.bvar).length = as.length + m := by
        simp only [List.length_append, List.length_map, List.length_range]
      rw [hlen, List.length_cons, List.drop_succ_cons]
      let rest := (ds'.drop as.length).foldr Expr.pi r
      have hcomm : instantiate (as.length + m) (lift 0 (as.length + m) a)
            (lift 0 m rest) =
          lift 0 m (instantiate as.length (lift 0 as.length a) rest) := by
        have hs : lift 0 m (lift 0 as.length a) = lift 0 (as.length + m) a :=
          lift_lift_merge m as.length 0 0 (Nat.le_refl 0) (by omega) a
        have hc := lift_instantiate_high_idx m 0 as.length
          (lift 0 as.length a) (Nat.zero_le _) rest
        rw [hs, Nat.add_comm m as.length] at hc
        exact hc.symm
      rw [hcomm]
      apply congrArg (lift 0 m)
      have hdropLen : (ds'.drop as.length).length = m := by
        have hdslen : ds'.length = as.length + m := peelPis_length _ B hpeel
        rw [List.length_drop, hdslen]
        omega
      have hsplit : (instDoms 0 a ds').drop as.length =
          instDoms as.length (lift 0 as.length a) (ds'.drop as.length) := by
        have happ : ds'.take as.length ++ ds'.drop as.length = ds' :=
          List.take_append_drop _ _
        have hstep := instDoms_drop 0 a (ds'.take as.length) (ds'.drop as.length)
        rw [happ, List.length_take, Nat.zero_add] at hstep
        have hle : as.length ≤ ds'.length := by
          have hdslen : ds'.length = as.length + m := peelPis_length _ B hpeel
          omega
        simpa [Nat.min_eq_left hle] using hstep
      have hbody := instantiate_foldr_pi as.length (lift 0 as.length a)
        (ds'.drop as.length) r
      rw [hdropLen] at hbody
      have hmerge : lift 0 m (lift 0 as.length a) = lift 0 (as.length + m) a :=
        lift_lift_merge m as.length 0 0 (Nat.le_refl 0) (by omega) a
      rw [hmerge] at hbody
      rw [← hsplit] at hbody
      exact hbody.symm

/-- `instantiateLevels` is a `foldr Expr.pi` congruence. -/
private theorem instantiateLevels_foldr_pi (ls : List Level) :
    (ds : List (Expr Nat)) → (r : Expr Nat) →
    instantiateLevels ls (ds.foldr Expr.pi r) =
      (ds.map (instantiateLevels ls)).foldr Expr.pi (instantiateLevels ls r)
  | [], _ => by
      simp only [List.foldr_nil, List.map_nil]
  | _ :: ds, r => by
      simp only [List.foldr_cons, List.map_cons, instantiateLevels]
      rw [instantiateLevels_foldr_pi ls ds r]

/-- C2 at a witness: the W-arm's `applyTel` image is `instPrefix` of the
level-instantiated stored field telescope, lifted across the leftover field
binders. No `exprClosedAt`. `telWhnfDom` of this image is still the walk. -/
theorem applyTel_ctorAfter_fieldTel {E : ResolvedEnv} (w : IotaWitnessS E) :
    applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
      some (instPrefix
        (w.preMajor.take w.nparams ++ (List.range w.fields.length).map Expr.bvar)
        (lift 0 w.fields.length
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)))) := by
  let ls := w.ls.take w.ctorMember.arity
  have hlen : (w.preMajor.take w.nparams).length = w.nparams := by
    rw [List.length_take, w.hpre, Nat.min_eq_left (by omega)]
  have hpeel := peelPis_instantiateLevels ls
    (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hpeel' : peelPis
      ((w.preMajor.take w.nparams).length + w.fields.length)
      (instantiateLevels ls w.ctorMember.mtype) =
      some (w.ctorDoms.map (instantiateLevels ls),
        instantiateLevels ls w.ctorResult) := by
    rw [hlen]
    exact hpeel
  rw [applyTel_instPrefix_rest (w.preMajor.take w.nparams) w.fields.length
    (instantiateLevels ls w.ctorMember.mtype) hpeel']
  apply congrArg some
  apply congrArg
    (instPrefix (w.preMajor.take w.nparams ++
      (List.range w.fields.length).map Expr.bvar))
  apply congrArg (lift 0 w.fields.length)
  rw [hlen, ← List.map_drop, ctorFieldTelRaw]
  exact (instantiateLevels_foldr_pi ls (w.ctorDoms.drop w.nparams)
    w.ctorResult).symm

/-! ## (3b) C3 — const head of a `.recursive 0` whnf, and `fieldsTelS` on the stored telescope

`fieldAnalyze_recursive_out` (sealed) sends `.recursive 0` to an empty
`piTelescopeFuel`, whose body `properFamilyFuel_true` shows is a const-headed
family application. That whnf is stable up to the analysis fuel
(`whnfFuel_mono`), which is the fuel `telWhnfDom` reads. glm's
`spine_img_const` (`RcicIotaFunRecWalkAgree`) is the image of an already
const-headed `foldApps` under `instPrefix`; it is not this lemma, and their
walk induction is still a draft. The whnf'd `fieldsTelS` conjunct on
`ctorAfter` stays theirs; the closedness-free `applyTel`/`instPrefix`
bridge is `applyTel_instPrefix_rest` above. -/

private theorem piTel_nil_whnf (E : ResolvedEnv) {fuel : Nat} {e w : Expr Nat}
    (h : piTelescopeFuel E fuel e = some ([], w)) :
    ∃ f, fuel = f + 1 ∧ whnfFuel E f e = some w := by
  cases fuel with
  | zero =>
      simp only [piTelescopeFuel] at h
      exact Option.noConfusion h
  | succ f =>
      refine ⟨f, rfl, ?_⟩
      simp only [piTelescopeFuel] at h
      revert h
      cases hw : whnfFuel E f e with
      | none =>
          intro h
          exact Option.noConfusion h
      | some w' =>
          intro h
          cases w' <;> simp only at h
          case pi A B =>
              revert h
              cases hp : piTelescopeFuel E f B with
              | none =>
                  intro h
                  simp only [hp] at h
                  exact Option.noConfusion h
              | some p =>
                  obtain ⟨ds', b'⟩ := p
                  intro h
                  simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
                  exact absurd h.1 (List.cons_ne_nil _ _)
          all_goals simp_all

/-- C3 per field: `.recursive 0` means `whnfFuel` returns a const-headed
    whnf. `nparams ≤ depth` is the witness's own depth (`fieldShapesFuel`
    starts at `nparams` and steps up). -/
theorem whnfFuel_some_const_of_recursive0 {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth T =
      .permitted (.recursive 0) idx)
    (hnp : nparams ≤ depth) :
    ∃ w, whnfFuel E fuel T = some w ∧ spineHeadConst w = true := by
  obtain ⟨doms, body, hpt, hlen, _, hproper⟩ := fieldAnalyze_recursive_out h
  have hnpt : nparams ≤ (doms.length + depth - 1) + 1 := by
    rw [hlen]
    omega
  obtain ⟨ls, args, hbody, _, _, _⟩ := properFamilyFuel_true hnpt hproper
  have hnil : doms = [] := by
    cases doms with
    | nil => rfl
    | cons _ _ =>
        rw [List.length_cons] at hlen
        exact absurd hlen (Nat.succ_ne_zero _)
  subst hnil
  obtain ⟨f, hf, hw⟩ := piTel_nil_whnf E hpt
  have hwFuel : whnfFuel E fuel T = some body :=
    whnfFuel_mono E (by omega) hw
  have hsc : spineHeadConst body = true := by
    rw [hbody]
    unfold spineHeadConst
    rw [appsSpine_foldApps_const]
  exact ⟨body, hwFuel, hsc⟩

/-- `telWhnfDom`'s `(whnfFuel …).getD` domain passes `shapeGuardS` at
    `.recursive 0`. -/
theorem spineHeadConst_whnf_of_recursive0 {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth T =
      .permitted (.recursive 0) idx)
    (hnp : nparams ≤ depth) :
    spineHeadConst ((whnfFuel E fuel T).getD T) = true := by
  obtain ⟨w, hw, hsc⟩ := whnfFuel_some_const_of_recursive0 h hnp
  rw [hw]
  exact hsc

/-- Pointwise `shapeGuardS` down a raw Π-telescope (bodies not yet instantiated). -/
def telShapeGuarded : List FieldShape → Expr Nat → Prop
  | [], _ => True
  | s :: ss, .pi A B => shapeGuardS A s = true ∧ telShapeGuarded ss B
  | _ :: _, _ => False

private theorem shapeGuardS_instantiate_of_noFun {A : Expr Nat} {s : FieldShape}
    (h : ∀ k, s ≠ .recursive (k + 1)) (hg : shapeGuardS A s = true)
    (j : Nat) (v : Expr Nat) :
    shapeGuardS (instantiate j v A) s = true := by
  cases s with
  | nonrecursive => rfl
  | recursive n =>
      cases n with
      | zero =>
          simp only [shapeGuardS] at hg ⊢
          exact spineHeadConst_instantiate j v A hg
      | succ k => exact absurd rfl (h k)

private theorem telShapeGuarded_instantiate {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes) (h : telShapeGuarded shapes T)
    (j : Nat) (v : Expr Nat) :
    telShapeGuarded shapes (instantiate j v T) := by
  induction shapes generalizing T j v with
  | nil => trivial
  | cons s ss ih =>
      cases T with
      | pi A B =>
          obtain ⟨hg, htail⟩ := h
          exact ⟨shapeGuardS_instantiate_of_noFun
              (hNF s (List.mem_cons_self s ss)) hg j v,
            ih (fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')) htail
              (j + 1) (lift 0 1 v)⟩
      | bvar _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | sort _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | const _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | app _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | lam _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | letE _ _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | lit _ =>
          unfold telShapeGuarded at h
          exact False.elim h

/-- `fieldsTelS` accepts a telescope whose domains already satisfy `shapeGuardS`,
    once `NoFunShapes` keeps the guard stable under the walk's `instantiate0`. -/
theorem fieldsTelS_of_telShapeGuarded {fields : List (Expr Nat)}
    {shapes : List FieldShape} {tel : Expr Nat}
    (hlen : fields.length = shapes.length) (hNF : NoFunShapes shapes)
    (h : telShapeGuarded shapes tel) :
    fieldsTelS fields shapes tel = true := by
  induction fields generalizing shapes tel with
  | nil =>
      cases shapes with
      | nil => rfl
      | cons _ ss =>
          rw [List.length_nil, List.length_cons] at hlen
          exact absurd hlen.symm (Nat.succ_ne_zero ss.length)
  | cons f fs ih =>
      cases shapes with
      | nil =>
          rw [List.length_cons, List.length_nil] at hlen
          exact absurd hlen (Nat.succ_ne_zero fs.length)
      | cons s ss =>
          have hlen' : fs.length = ss.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ.inj hlen
          have hNF' : NoFunShapes ss :=
            fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')
          cases tel with
          | pi A B =>
              obtain ⟨hg, htail⟩ := h
              show (shapeGuardS A s &&
                  fieldsTelS fs ss (instantiate0 f B)) = true
              rw [Bool.and_eq_true]
              exact ⟨hg, ih hlen' hNF'
                (telShapeGuarded_instantiate hNF' htail 0 f)⟩
          | bvar _ =>
              unfold telShapeGuarded at h
              exact False.elim h
          | sort _ =>
              unfold telShapeGuarded at h
              exact False.elim h
          | const _ _ =>
              unfold telShapeGuarded at h
              exact False.elim h
          | app _ _ =>
              unfold telShapeGuarded at h
              exact False.elim h
          | lam _ _ =>
              unfold telShapeGuarded at h
              exact False.elim h
          | letE _ _ _ =>
              unfold telShapeGuarded at h
              exact False.elim h
          | lit _ =>
              unfold telShapeGuarded at h
              exact False.elim h

private theorem fieldShapesFuel_cons {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {Ts : List (Expr Nat)} {shapes : List FieldShape}
    (h : fieldShapesFuel E fuel fam nuniv nparams nindices depth (T :: Ts) =
      some shapes) :
    ∃ s idx ss,
      fieldAnalyze E fuel fam nuniv nparams nindices depth T = .permitted s idx ∧
      fieldShapesFuel E fuel fam nuniv nparams nindices (depth + 1) Ts = some ss ∧
      shapes = s :: ss := by
  simp only [fieldShapesFuel] at h
  cases ha : fieldAnalyze E fuel fam nuniv nparams nindices depth T with
  | permitted s idx =>
      rw [ha] at h
      cases hr : fieldShapesFuel E fuel fam nuniv nparams nindices (depth + 1) Ts with
      | none =>
          rw [hr] at h
          exact Option.noConfusion h
      | some ss =>
          rw [hr] at h
          injection h with hs
          exact ⟨s, idx, ss, rfl, rfl, hs.symm⟩
  | refused _ =>
      rw [ha] at h
      exact Option.noConfusion h
  | unresolved =>
      rw [ha] at h
      exact Option.noConfusion h

theorem telShapeGuarded_telWhnf_of_shapes {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices : Nat} {result : Expr Nat} (depth : Nat)
    (doms : List (Expr Nat)) {shapes : List FieldShape}
    (hsh : fieldShapesFuel E fuel fam nuniv nparams nindices depth doms = some shapes)
    (hNF : NoFunShapes shapes) (hnp : nparams ≤ depth) :
    telShapeGuarded shapes (telWhnfDom E fuel (doms.foldr Expr.pi result)) := by
  induction doms generalizing shapes depth with
  | nil =>
      simp only [fieldShapesFuel] at hsh
      injection hsh with hs
      subst hs
      trivial
  | cons T Ts ih =>
      obtain ⟨s, _, ss, ha, hr, hs⟩ := fieldShapesFuel_cons hsh
      subst hs
      have hRest : NoFunShapes ss :=
        fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')
      refine ⟨?_, ih (depth + 1) hr hRest (Nat.le_succ_of_le hnp)⟩
      cases s with
      | nonrecursive => rfl
      | recursive k =>
          cases k with
          | zero =>
              simp only [shapeGuardS]
              exact spineHeadConst_whnf_of_recursive0 ha hnp
          | succ j =>
              exact absurd rfl
                (hNF (.recursive (j + 1)) (List.mem_cons_self _ _) j)

/-- C3 on a stored field telescope: `NoFunShapes` plus the shapes read at
    `depth ≥ nparams` make `fieldsTelS` accept the whnf'd `foldr Expr.pi`. -/
theorem fieldsTelS_storedTel_of_noFun {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {result : Expr Nat}
    {doms : List (Expr Nat)} {shapes : List FieldShape} {fields : List (Expr Nat)}
    (hlen : fields.length = doms.length)
    (hsh : fieldShapesFuel E fuel fam nuniv nparams nindices depth doms = some shapes)
    (hNF : NoFunShapes shapes) (hnp : nparams ≤ depth) :
    fieldsTelS fields shapes
      (telWhnfDom E fuel (doms.foldr Expr.pi result)) = true :=
  fieldsTelS_of_telShapeGuarded
    (hlen.trans (fieldShapesFuel_length E doms hsh).symm) hNF
    (telShapeGuarded_telWhnf_of_shapes depth doms hsh hNF hnp)

/-- C3 at a witness, on the admission telescope `ctorFieldTelRaw`. The W-arm's
    `ctorAfter` is the `instPrefix` image of `instantiateLevels` on that
    telescope (`applyTel_ctorAfter_fieldTel`); `telWhnfDom` of the image is
    still the walk. -/
theorem fieldsTelS_ctorFieldTelRaw_of_noFun {E : ResolvedEnv} (w : IotaWitnessS E)
    (hNF : NoFunShapes w.shapes) :
    fieldsTelS w.fields w.shapes
      (telWhnfDom E w.fuel
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
  have hpeelLen : w.ctorDoms.length = w.nparams + w.fields.length :=
    peelPis_length (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hdrop : (w.ctorDoms.drop w.nparams).length = w.fields.length := by
    rw [List.length_drop, hpeelLen]
    omega
  exact fieldsTelS_storedTel_of_noFun hdrop.symm w.hshapes hNF (Nat.le_refl _)

/-! ## (4) C4 + C5b — the minor marker instantiates to `preMajor[np+1+ctorIdx]` -/

/-- C4: the minor lookup always exists (`ctorIdx < nMinors` inside
    `np + 1 + nM + ni = preMajor.length`). -/
theorem preMajor_minor_exists {E : ResolvedEnv} (w : IotaWitnessS E) :
    ∃ m, w.preMajor[w.nparams + 1 + w.ctorIdx]? = some m := by
  have hlt : w.nparams + 1 + w.ctorIdx < w.preMajor.length := by
    rw [w.hpre]; have := w.hidx; omega
  exact ⟨w.preMajor[w.nparams + 1 + w.ctorIdx]'hlt,
    List.getElem?_eq_getElem hlt⟩

/-- C5b: the canonical minor marker
    `bvar (fl + ni + (nM-1-ctorIdx))` — the slot of the `ctorIdx`-th minor in
    the canonical equation context — `instPrefix`-maps to
    `preMajor[np + 1 + ctorIdx]` (`count-1-j = np+1+ctorIdx`). -/
theorem instPrefix_minor_marker {E : ResolvedEnv} (w : IotaWitnessS E)
    {m : Expr Nat}
    (hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some m) :
    instPrefix (w.preMajor ++ w.fields)
        (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx))) =
      m := by
  apply instPrefix_bvar_lt
  · rw [List.length_append, w.hpre]
    have := w.hidx
    omega
  · rw [List.length_append, w.hpre]
    have hidx' :
        w.nparams + 1 + w.nMinors + w.nindices + w.fields.length - 1 -
          (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)) =
        w.nparams + 1 + w.ctorIdx := by
      have := w.hidx
      omega
    rw [hidx']
    have hlt : w.nparams + 1 + w.ctorIdx < w.preMajor.length := by
      rw [w.hpre]; have := w.hidx; omega
    rw [List.getElem?_append_left hlt]
    exact hm

/-- A field bvar `k < fields.length` under `instPrefix (pre ++ fields)`
    is `fields[fields.length - 1 - k]`. Innermost `bvar 0` is the last
    field. No `exprClosedAt`. `closure_claim` stays 0. -/
theorem instPrefix_append_fieldBvar {pre fields : List (Expr Nat)}
    {k : Nat} {a : Expr Nat} (hk : k < fields.length)
    (hget : fields[fields.length - 1 - k]? = some a) :
    instPrefix (pre ++ fields) (.bvar k) = a := by
  apply instPrefix_bvar_lt
  · rw [List.length_append]
    omega
  · rw [List.length_append]
    have hidx :
        pre.length + fields.length - 1 - k =
          pre.length + (fields.length - 1 - k) := by omega
    rw [hidx]
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    have hsub :
        pre.length + (fields.length - 1 - k) - pre.length =
          fields.length - 1 - k := by omega
    rw [hsub]
    exact hget

/-! ## (5) C5a — `iotaRhsOfS` factors through `foldApps` -/

/-- The schema's `iotaOpenRhs` success decomposes into the `iotaArgs` walk and
    the canonical `foldApps`. `foldApps_instantiateLevels` is the sealed
    owner of the level distribution. -/
theorem iotaRhsOfS_eq_fold {E : ResolvedEnv} (w : IotaWitnessS E)
    {args : List (Expr Nat)} {m : Expr Nat}
    (hargs : iotaArgs E w.fuel
        (.const w.recRef (canonRecLevels w.recMember.arity))
        (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
        w.nparams w.nMinors w.shapes (fieldBvars w.fields.length)
        (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = some args)
    (hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some m) :
    iotaRhsOfS w =
      foldApps m
        (args.map (fun a =>
          instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a))) := by
  have hsc : w.schema = foldApps
      (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
      args := by
    have h := w.hschema
    simp only [iotaOpenRhs, Option.map_eq_some'] at h
    obtain ⟨a, ha, hfold⟩ := h
    rw [hargs] at ha
    injection ha with ha'
    subst ha'
    exact hfold.symm
  unfold iotaRhsOfS
  rw [hsc, foldApps_instantiateLevels, instPrefix_foldApps]
  simp only [instantiateLevels]
  rw [instPrefix_minor_marker w hm, List.map_map]
  rfl

/-! ## (6) C5c — cited, not re-proved

`instPrefix_instLs` (`RcicIotaShape`, already in `sealedTheorems`) is the
unconditional commutation

  `instantiateLevels ls (instPrefix xs e)
     = instPrefix (xs.map (instantiateLevels ls)) (instantiateLevels ls e)`.

The W-arm assembly calls that name. glm's `canonRecLevels_instLevel` /
`preMajorBvars_map_instPrefix` (`RcicIotaFunRecWalk` on `glm/nofunrec-s6`)
stay on their branch; C5d's walk agreement is theirs. -/

/-! ## (7) Assembly — C1, C2 and C4, with the walk image left open

`ctorAfterFieldTel` is the image `applyTel_ctorAfter_fieldTel` names.
`ctorAfterFieldTel_eq_instPrefix` cancels the identity field-bvar suffix, so
the image is parameter `instPrefix` of the level-instantiated stored field
telescope. Under `NoFunShapes` the W-union recognizer reduces to `fieldsTelS`
and `rhsEq` at `telWhnfDom` of that image. Those two are glm's walk
(`iotaArgs_agree` does not elaborate here; (d) REL₀ and (e) the witness
corollary are still theirs, and are not re-proved). `EnvWfT` is not a
premise: every conjunct discharged here is data on the witness.
`closure_claim` stays 0. -/

/-- The W-arm `applyTel` image: `instPrefix` of `instantiateLevels` on the
    stored field telescope. The leftover binders are
    `(List.range fl).map Expr.bvar`. -/
def ctorAfterFieldTel {E : ResolvedEnv} (w : IotaWitnessS E) : Expr Nat :=
  instPrefix
    (w.preMajor.take w.nparams ++ (List.range w.fields.length).map Expr.bvar)
    (lift 0 w.fields.length
      (instantiateLevels (w.ls.take w.ctorMember.arity)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)))

theorem applyTel_eq_ctorAfterFieldTel {E : ResolvedEnv} (w : IotaWitnessS E) :
    applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
      some (ctorAfterFieldTel w) :=
  applyTel_ctorAfter_fieldTel w

/-- The leftover field bvars are an identity prefix: they cancel `lift 0 fl`.
    `ctorAfterFieldTel` is `instPrefix` of the parameter prefix on the
    level-instantiated stored field telescope. No `exprClosedAt`.
    `closure_claim` stays 0. -/
theorem ctorAfterFieldTel_eq_instPrefix {E : ResolvedEnv} (w : IotaWitnessS E) :
    ctorAfterFieldTel w =
      instPrefix (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) := by
  unfold ctorAfterFieldTel
  have hlen :
      ((List.range w.fields.length).map (Expr.bvar : Nat → Expr Nat)).length =
        w.fields.length := by
    rw [List.length_map, List.length_range]
  rw [instPrefix_append, hlen, instOff_lift]
  have hlift :=
    instPrefix_lift ((List.range w.fields.length).map (Expr.bvar : Nat → Expr Nat))
      (instPrefix (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)))
  rw [hlen] at hlift
  exact hlift

/-- C1, C2 and C4 at one frec-free witness. The premises are C3 and C5 at
    `telWhnfDom` of `ctorAfterFieldTel`. -/
theorem iotaWitnessSAnnDW_of_noFun_image {E : ResolvedEnv} (w : IotaWitnessS E)
    (hNF : NoFunShapes w.shapes)
    (hTel : fieldsTelS w.fields w.shapes
        (telWhnfDom E w.fuel (ctorAfterFieldTel w)) = true)
    (hRhs : ∀ minor,
        w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor →
        iotaRhsOfS w =
          foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
            w.nparams w.nMinors w.fields w.shapes
            (telWhnfDom E w.fuel (ctorAfterFieldTel w)))) :
    iotaWitnessSAnnDW E w = true := by
  have hlen : (w.ctorDoms.drop w.nparams).length = w.shapes.length :=
    (fieldShapesFuel_length E (w.ctorDoms.drop w.nparams) w.hshapes).symm
  have hD : iotaWitnessSAnnDArmW E w = true := by
    unfold iotaWitnessSAnnDArmW
    rw [drecFragCheck_of_noFun hlen hNF, Bool.true_and]
    rw [applyTel_eq_ctorAfterFieldTel w]
    dsimp only
    rw [Bool.and_eq_true]
    refine ⟨hTel, ?_⟩
    obtain ⟨minor, hm⟩ := preMajor_minor_exists w
    rw [hm]
    exact decide_eq_true (hRhs minor hm)
  unfold iotaWitnessSAnnDW
  rw [hD, Bool.or_true]

/-- The per-env certificate from the walk image at every frec-free witness.
    `EnvWfT` is not a premise of this reduction. -/
theorem envCorrAnnDWC_of_image {E : ResolvedEnv}
    (h : ∀ w : IotaWitnessS E, NoFunShapes w.shapes →
      fieldsTelS w.fields w.shapes
          (telWhnfDom E w.fuel (ctorAfterFieldTel w)) = true ∧
        ∀ minor, w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor →
          iotaRhsOfS w =
            foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
              w.nparams w.nMinors w.fields w.shapes
              (telWhnfDom E w.fuel (ctorAfterFieldTel w)))) :
    EnvCorrAnnDWC E :=
  fun w hNF =>
    iotaWitnessSAnnDW_of_noFun_image w hNF (h w hNF).1 (h w hNF).2

/-! ## (8) Level-arity alignment from `EnvWfT`

The W-arm instantiates the stored constructor type at
`w.ls.take w.ctorMember.arity`. glm's (d) lists
`instantiateLevels ls ctorType = instantiateLevels (ls.take arity) ctorType`
as a premise. `instantiateLevels_take` is that equation once the type is
level-bounded at the arity, and `envWfT_levels` is the bound.
`closure_claim` stays 0. -/

/-- On an `EnvWfT` environment, instantiating a constructor's stored type
    at a level list agrees with instantiating it at the arity prefix. -/
theorem instantiateLevels_ctorMtype_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) (lvls : List Level) :
    instantiateLevels lvls w.ctorMember.mtype =
      instantiateLevels (lvls.take w.ctorMember.arity)
        w.ctorMember.mtype :=
  instantiateLevels_take w.ctorMember.arity lvls w.ctorMember.mtype
    (envWfT_levels hW w.ctorRef w.ctorMember w.hctor).1

/-- The W-arm `applyTel` at the witness's full level list is
    `ctorAfterFieldTel`. The recognizer writes `ls.take arity`; glm's (d)
    writes the full list and takes the level equation as a premise.
    `EnvWfT` discharges that premise. `closure_claim` stays 0. -/
theorem applyTel_eq_ctorAfterFieldTel_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) :
    applyTel (w.preMajor.take w.nparams)
        (instantiateLevels w.ls w.ctorMember.mtype) =
      some (ctorAfterFieldTel w) := by
  rw [instantiateLevels_ctorMtype_of_envWfT hW w w.ls]
  exact applyTel_eq_ctorAfterFieldTel w

/-! ## (9) The cancelled image, named

`ctorAfterFieldTel_eq_instPrefix` says the W-arm image is parameter
`instPrefix` of the level-instantiated stored field telescope. Naming that
term lets the walk premises be stated at the image glm's (d)/(e) will
produce, and transported back to `ctorAfterFieldTel`.
`closure_claim` stays 0. -/

/-- Parameter `instPrefix` of the level-instantiated stored field telescope.
    Equal to `ctorAfterFieldTel` by cancellation of the identity suffix. -/
def ctorFieldTelInst {E : ResolvedEnv} (w : IotaWitnessS E) : Expr Nat :=
  instPrefix (w.preMajor.take w.nparams)
    (instantiateLevels (w.ls.take w.ctorMember.arity)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))

theorem ctorAfterFieldTel_eq_ctorFieldTelInst {E : ResolvedEnv}
    (w : IotaWitnessS E) :
    ctorAfterFieldTel w = ctorFieldTelInst w :=
  ctorAfterFieldTel_eq_instPrefix w

/-- `EnvCorrAnnDWC` from `fieldsTelS` and `rhsEq` at `telWhnfDom` of
    `ctorFieldTelInst`. The transport is the identity-suffix cancellation.
    `EnvWfT` is not a premise. `closure_claim` stays 0. -/
theorem envCorrAnnDWC_of_instPrefix_image {E : ResolvedEnv}
    (h : ∀ w : IotaWitnessS E, NoFunShapes w.shapes →
      fieldsTelS w.fields w.shapes
          (telWhnfDom E w.fuel (ctorFieldTelInst w)) = true ∧
        ∀ minor, w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor →
          iotaRhsOfS w =
            foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
              w.nparams w.nMinors w.fields w.shapes
              (telWhnfDom E w.fuel (ctorFieldTelInst w)))) :
    EnvCorrAnnDWC E := by
  refine envCorrAnnDWC_of_image ?_
  intro w hNF
  have himg := h w hNF
  rw [← ctorAfterFieldTel_eq_ctorFieldTelInst] at himg
  exact himg

/-! ## (10) `whnfFuel` commutes with `instantiateLevels`

Levels do not bind and do not change a constant's reference, so a
fuel-bounded whnf commutes with `instantiateLevels` once every unfolded
constant carries its member's arity (`ConstsArity`) and every transparent
body does too (`EnvConstsArity`). This is the level half of the
`telWhnfDom` transport onto `ctorFieldTelInst`. It is not the walk:
no `iotaArgs`, no `exprClosedAt`. `closure_claim` stays 0. -/

/-- Every constant occurrence carries its member's arity. The erased twin
    of `ConstsArityA`. -/
def ConstsArity (E : ResolvedEnv) : Expr Nat → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r ms => ∃ m, E.members r = some m ∧ ms.length = m.arity
  | .app f x => ConstsArity E f ∧ ConstsArity E x
  | .lam a b => ConstsArity E a ∧ ConstsArity E b
  | .pi a b => ConstsArity E a ∧ ConstsArity E b
  | .letE a v b => ConstsArity E a ∧ ConstsArity E v ∧ ConstsArity E b
  | .lit _ => True

/-- Transparent bodies obey `ConstsArity`. Definitions are the members
    `whnfFuel` unfolds. -/
def EnvConstsArity (E : ResolvedEnv) : Prop :=
  ∀ r m b, E.members r = some m → m.body = some b → ConstsArity E b

private theorem ConstsArity_instantiateLevels {E : ResolvedEnv} (ls : List Level) :
    (e : Expr Nat) → ConstsArity E e → ConstsArity E (instantiateLevels ls e)
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .const _ ms, h => by
      obtain ⟨m, hm, hlen⟩ := h
      exact ⟨m, hm, by rw [List.length_map]; exact hlen⟩
  | .app f x, h =>
      ⟨ConstsArity_instantiateLevels ls f h.1, ConstsArity_instantiateLevels ls x h.2⟩
  | .lam a b, h =>
      ⟨ConstsArity_instantiateLevels ls a h.1, ConstsArity_instantiateLevels ls b h.2⟩
  | .pi a b, h =>
      ⟨ConstsArity_instantiateLevels ls a h.1, ConstsArity_instantiateLevels ls b h.2⟩
  | .letE a v b, h =>
      ⟨ConstsArity_instantiateLevels ls a h.1, ConstsArity_instantiateLevels ls v h.2.1,
        ConstsArity_instantiateLevels ls b h.2.2⟩
  | .lit _, _ => trivial

private theorem ConstsArity_lift {E : ResolvedEnv} (c a : Nat) :
    (e : Expr Nat) → ConstsArity E e → ConstsArity E (lift c a e)
  | .bvar _, _ => by
      unfold lift
      split <;> trivial
  | .sort _, _ => trivial
  | .const _ _, h => h
  | .app f x, h => ⟨ConstsArity_lift c a f h.1, ConstsArity_lift c a x h.2⟩
  | .lam A B, h => ⟨ConstsArity_lift c a A h.1, ConstsArity_lift (c + 1) a B h.2⟩
  | .pi A B, h => ⟨ConstsArity_lift c a A h.1, ConstsArity_lift (c + 1) a B h.2⟩
  | .letE A v B, h =>
      ⟨ConstsArity_lift c a A h.1, ConstsArity_lift c a v h.2.1,
        ConstsArity_lift (c + 1) a B h.2.2⟩
  | .lit _, _ => trivial

private theorem ConstsArity_instantiate {E : ResolvedEnv} (j : Nat) (v : Expr Nat)
    (hv : ConstsArity E v) :
    (e : Expr Nat) → ConstsArity E e → ConstsArity E (instantiate j v e)
  | .bvar _, _ => by
      simp only [instantiate]
      split
      · exact hv
      · split <;> trivial
  | .sort _, _ => trivial
  | .const _ _, h => h
  | .app f x, h =>
      ⟨ConstsArity_instantiate j v hv f h.1, ConstsArity_instantiate j v hv x h.2⟩
  | .lam A B, h =>
      ⟨ConstsArity_instantiate j v hv A h.1,
        ConstsArity_instantiate (j + 1) (lift 0 1 v) (ConstsArity_lift 0 1 v hv) B h.2⟩
  | .pi A B, h =>
      ⟨ConstsArity_instantiate j v hv A h.1,
        ConstsArity_instantiate (j + 1) (lift 0 1 v) (ConstsArity_lift 0 1 v hv) B h.2⟩
  | .letE A val B, h =>
      ⟨ConstsArity_instantiate j v hv A h.1, ConstsArity_instantiate j v hv val h.2.1,
        ConstsArity_instantiate (j + 1) (lift 0 1 v) (ConstsArity_lift 0 1 v hv) B h.2.2⟩
  | .lit _, _ => trivial

private theorem ConstsArity_foldApps {E : ResolvedEnv} (f : Expr Nat)
    (hf : ConstsArity E f) :
    (xs : List (Expr Nat)) → (∀ x ∈ xs, ConstsArity E x) →
      ConstsArity E (foldApps f xs)
  | [], _ => hf
  | x :: xs, hxs =>
      ConstsArity_foldApps (.app f x) ⟨hf, hxs x (List.mem_cons_self x xs)⟩ xs
        (fun y hy => hxs y (List.mem_cons_of_mem x hy))

private theorem ConstsArity_appsSpine {E : ResolvedEnv} :
    (e : Expr Nat) → ConstsArity E e →
      ConstsArity E (appsSpine e).1 ∧ ∀ a ∈ (appsSpine e).2, ConstsArity E a
  | .bvar _, _ => ⟨trivial, fun _ ha => by cases ha⟩
  | .sort _, _ => ⟨trivial, fun _ ha => by cases ha⟩
  | .const _ _, h => ⟨h, fun _ ha => by cases ha⟩
  | .lit _, _ => ⟨trivial, fun _ ha => by cases ha⟩
  | .lam _ _, h => ⟨h, fun _ ha => by cases ha⟩
  | .pi _ _, h => ⟨h, fun _ ha => by cases ha⟩
  | .letE _ _ _, h => ⟨h, fun _ ha => by cases ha⟩
  | .app f x, h => by
      obtain ⟨h1, h2⟩ := ConstsArity_appsSpine f h.1
      refine ⟨h1, ?_⟩
      intro a ha
      have ha' : a ∈ (appsSpine f).2 ∨ a = x := by
        simpa [appsSpine] using ha
      cases ha' with
      | inl ha => exact h2 a ha
      | inr heq =>
          subst heq
          exact h.2

/-- δ-unfolding commutes with an outer level substitution. The body's
    level bound is `EnvLevelsT`; the constant's level-list length is
    `ConstsArity`. -/
theorem transparentBody_instantiateLevels {E : ResolvedEnv}
    (hEL : EnvLevelsT E) (ls : List Level) (r : Nat) (ms : List Level)
    (hok : ConstsArity E (.const r ms)) :
    transparentBody E r (ms.map (instLevel ls)) =
      (transparentBody E r ms).map (instantiateLevels ls) := by
  obtain ⟨m, hmem, hlen⟩ := hok
  simp only [transparentBody, hmem]
  cases htr : transparent m.mclass with
  | false =>
      dsimp [htr]
  | true =>
      dsimp [htr]
      cases hb : m.body with
      | none => rfl
      | some b =>
          exact congrArg some
            (instantiateLevels_compose ls ms b
              (by rw [hlen]; exact (hEL r m hmem).2 b hb)).symm

private theorem ConstsArity_transparentBody {E : ResolvedEnv}
    (hEA : EnvConstsArity E) {r : Nat} {ms : List Level} {body : Expr Nat}
    (hb : transparentBody E r ms = some body)
    (hok : ConstsArity E (.const r ms)) :
    ConstsArity E body := by
  obtain ⟨m, hmem, _⟩ := hok
  simp only [transparentBody, hmem] at hb
  cases htr : transparent m.mclass with
  | false =>
      rw [htr] at hb
      cases hb
  | true =>
      rw [htr] at hb
      cases hbod : m.body with
      | none =>
          rw [hbod] at hb
          cases hb
      | some b =>
          rw [hbod] at hb
          cases hb
          exact ConstsArity_instantiateLevels ms b (hEA r m b hmem hbod)

/-- `whnfFuel` commutes with `instantiateLevels`. Fuel induction; the δ
    step is `transparentBody_instantiateLevels`, and β/ζ are
    `instantiateLevels_instantiate0`. -/
theorem whnfFuel_instantiateLevels {E : ResolvedEnv}
    (hEL : EnvLevelsT E) (hEA : EnvConstsArity E) (ls : List Level) :
    (fuel : Nat) → (e : Expr Nat) → ConstsArity E e →
      whnfFuel E fuel (instantiateLevels ls e) =
        (whnfFuel E fuel e).map (instantiateLevels ls)
  | 0, _, _ => rfl
  | fuel + 1, e, hok => by
      simp only [whnfFuel]
      rw [appsSpine_instantiateLevels]
      cases hsp : appsSpine e with
      | mk head args =>
        cases head with
        | lam A B =>
            cases args with
            | nil => rfl
            | cons x xs =>
                obtain ⟨hHead, hArgs⟩ := ConstsArity_appsSpine e hok
                rw [hsp] at hHead hArgs
                have hokRed : ConstsArity E (foldApps (instantiate0 x B) xs) :=
                  ConstsArity_foldApps (instantiate0 x B)
                    (ConstsArity_instantiate 0 x
                      (hArgs x (List.mem_cons_self x xs)) B hHead.2)
                    xs (fun y hy => hArgs y (List.mem_cons_of_mem x hy))
                show whnfFuel E fuel (foldApps
                    (instantiate0 (instantiateLevels ls x) (instantiateLevels ls B))
                    (xs.map (instantiateLevels ls))) =
                  Option.map (instantiateLevels ls)
                    (whnfFuel E fuel (foldApps (instantiate0 x B) xs))
                rw [← instantiateLevels_instantiate0, ← foldApps_instantiateLevels]
                exact whnfFuel_instantiateLevels hEL hEA ls fuel _ hokRed
        | letE A v B =>
            obtain ⟨hHead, hArgs⟩ := ConstsArity_appsSpine e hok
            rw [hsp] at hHead hArgs
            have hokRed : ConstsArity E (foldApps (instantiate0 v B) args) :=
              ConstsArity_foldApps (instantiate0 v B)
                (ConstsArity_instantiate 0 v hHead.2.1 B hHead.2.2) args hArgs
            show whnfFuel E fuel (foldApps
                (instantiate0 (instantiateLevels ls v) (instantiateLevels ls B))
                (args.map (instantiateLevels ls))) =
              Option.map (instantiateLevels ls)
                (whnfFuel E fuel (foldApps (instantiate0 v B) args))
            rw [← instantiateLevels_instantiate0, ← foldApps_instantiateLevels]
            exact whnfFuel_instantiateLevels hEL hEA ls fuel _ hokRed
        | const r ms =>
            obtain ⟨hHead, hArgs⟩ := ConstsArity_appsSpine e hok
            rw [hsp] at hHead hArgs
            show (match transparentBody E r (ms.map (instLevel ls)) with
                | some body => whnfFuel E fuel
                    (foldApps body (args.map (instantiateLevels ls)))
                | none => some (instantiateLevels ls e)) =
              Option.map (instantiateLevels ls) (match transparentBody E r ms with
                | some body => whnfFuel E fuel (foldApps body args)
                | none => some e)
            rw [transparentBody_instantiateLevels hEL ls r ms hHead]
            cases hb : transparentBody E r ms with
            | none => rfl
            | some body =>
                have hokFold : ConstsArity E (foldApps body args) :=
                  ConstsArity_foldApps body
                    (ConstsArity_transparentBody hEA hb hHead) args hArgs
                show whnfFuel E fuel (foldApps (instantiateLevels ls body)
                    (args.map (instantiateLevels ls))) =
                  Option.map (instantiateLevels ls)
                    (whnfFuel E fuel (foldApps body args))
                rw [← foldApps_instantiateLevels]
                exact whnfFuel_instantiateLevels hEL hEA ls fuel _ hokFold
        | bvar _ => rfl
        | sort _ => rfl
        | pi _ _ => rfl
        | app _ _ => rfl
        | lit _ => rfl

/-- Domain-wise, `telWhnfDom` commutes with `instantiateLevels`. -/
theorem telWhnfDom_instantiateLevels {E : ResolvedEnv}
    (hEL : EnvLevelsT E) (hEA : EnvConstsArity E) (ls : List Level) (fuel : Nat) :
    (e : Expr Nat) → ConstsArity E e →
      telWhnfDom E fuel (instantiateLevels ls e) =
        instantiateLevels ls (telWhnfDom E fuel e)
  | .pi A B, h => by
      have hW := whnfFuel_instantiateLevels hEL hEA ls fuel A h.1
      have hB := telWhnfDom_instantiateLevels hEL hEA ls fuel B h.2
      simp only [telWhnfDom, instantiateLevels, hW, hB]
      cases whnfFuel E fuel A <;> rfl
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

/-! ## (11) `ConstsArity` from typing

`hasTyT_constsArity` is the erased twin of `hasTyA_constsArity`. A literal
is `ConstsArity` outright: the predicate does not read `natExpand`.
`ConstsArity_extend` is monotonicity across a fresh `extendEnv`.
`closure_claim` stays 0. -/

theorem hasTyT_constsArity {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → ConstsArity E e
  | _, _, _, .sort _ _ => trivial
  | _, _, _, .bvar _ _ _ _ => trivial
  | _, _, _, .const _ _ _ m hres hlen _ => ⟨m, hres, hlen⟩
  | _, _, _, .pi _ _ _ _ _ hA hB => ⟨hasTyT_constsArity hA, hasTyT_constsArity hB⟩
  | _, _, _, .lam _ _ _ _ _ hA hb => ⟨hasTyT_constsArity hA, hasTyT_constsArity hb⟩
  | _, _, _, .app _ _ _ _ _ hf ha => ⟨hasTyT_constsArity hf, hasTyT_constsArity ha⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb =>
      ⟨hasTyT_constsArity hA, hasTyT_constsArity hv, hasTyT_constsArity hb⟩
  | _, _, _, .lit _ _ _ _ => trivial
  | _, _, _, .conv _ _ _ _ _ h _ => hasTyT_constsArity h

private theorem ConstsArity_extend {E : ResolvedEnv} (r : Nat) (m : CheckedMember)
    (hfresh : E.members r = none) :
    (e : Expr Nat) → ConstsArity E e → ConstsArity (extendEnv E r m) e
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .const r' ms, h => by
      obtain ⟨m', hm, hlen⟩ := h
      simp only [ConstsArity]
      by_cases heq : r' = r
      · subst heq
        rw [hfresh] at hm
        cases hm
      · refine ⟨m', ?_, hlen⟩
        simp only [extendEnv]
        rw [if_neg heq]
        exact hm
  | .app f x, h =>
      ⟨ConstsArity_extend r m hfresh f h.1, ConstsArity_extend r m hfresh x h.2⟩
  | .lam a b, h =>
      ⟨ConstsArity_extend r m hfresh a h.1, ConstsArity_extend r m hfresh b h.2⟩
  | .pi a b, h =>
      ⟨ConstsArity_extend r m hfresh a h.1, ConstsArity_extend r m hfresh b h.2⟩
  | .letE a v b, h =>
      ⟨ConstsArity_extend r m hfresh a h.1,
        ConstsArity_extend r m hfresh v h.2.1,
        ConstsArity_extend r m hfresh b h.2.2⟩
  | .lit _, _ => trivial

/-! ## (12) `EnvConstsArity` from `EnvWfT`

A definition, theorem, or opaque body is typed in the environment it extends,
so `hasTyT_constsArity` gives `ConstsArity` there and `ConstsArity_extend`
carries it across the fresh binding. A group member stores `body = none`.
`closure_claim` stays 0. -/

private theorem envConstsArity_extend_member {E : ResolvedEnv} (r : Nat)
    (mNew : CheckedMember) (hfresh : E.members r = none) (hE : EnvConstsArity E)
    (hnew : ∀ b, mNew.body = some b → ConstsArity E b) :
    EnvConstsArity (extendEnv E r mNew) := by
  intro r' m b hm hb
  by_cases heq : r' = r
  · have hsm : some mNew = some m := by simpa [extendEnv, heq] using hm
    have hmEq : mNew = m := by injection hsm
    rw [← hmEq] at hb
    exact ConstsArity_extend r mNew hfresh b (hnew b hb)
  · have hmE : E.members r' = some m := by simpa [extendEnv, heq] using hm
    exact ConstsArity_extend r mNew hfresh b (hE r' m b hmE hb)

private theorem envConstsArity_groupMembers {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {rows : List (Nat × CheckedMember)} →
    EnvConstsArity E → GroupMembersT S E rows E' → EnvConstsArity E'
  | _, _, _, hE, .nil _ => hE
  | _, _, _, hE, .cons _ r m _ _ hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ hrest =>
      envConstsArity_groupMembers
        (envConstsArity_extend_member r m hfresh hE (fun b hb => by
          rw [hnobody] at hb
          cases hb))
        hrest

theorem envConstsArity_of_envWfT {E : ResolvedEnv} : EnvWfT E → EnvConstsArity E
  | .empty => by
      intro _ _ _ hm _
      simp [emptyEnv] at hm
  | .axiom (arity := arity) E r A _ hE hfresh _ _ _ =>
      envConstsArity_extend_member r ⟨.axiomM, arity, A, none⟩ hfresh
        (envConstsArity_of_envWfT hE) (fun _ hb => by cases hb)
  | .definition E r A v _ hE hfresh _ hv _ _ _ _ =>
      envConstsArity_extend_member r ⟨.definitionM, 0, A, some v⟩ hfresh
        (envConstsArity_of_envWfT hE) (fun _ hb => by
          cases hb
          exact hasTyT_constsArity hv)
  | .thm E r A p hE hfresh _ hp _ _ _ _ =>
      envConstsArity_extend_member r ⟨.theoremM, 0, A, some p⟩ hfresh
        (envConstsArity_of_envWfT hE) (fun _ hb => by
          cases hb
          exact hasTyT_constsArity hp)
  | .opaque E r A v _ hE hfresh _ hv _ _ _ _ =>
      envConstsArity_extend_member r ⟨.opaqueM, 0, A, some v⟩ hfresh
        (envConstsArity_of_envWfT hE) (fun _ hb => by
          cases hb
          exact hasTyT_constsArity hv)
  | .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      envConstsArity_groupMembers (envConstsArity_of_envWfT hE) hmem

/-! ## (13) `ConstsArity` of `ctorFieldTelRaw`

`envWfT_mtypeSortTyped` sort-types the constructor's stored type in the
final environment. `peelPis` splits that `ConstsArity` across the
domains and the result, and `foldr Expr.pi` rebuilds the field suffix
`ctorFieldTelRaw`. `telWhnfDom_instantiateLevels` then moves the level
substitution out of `telWhnfDom` at that telescope. Parameter
`instPrefix` is not moved. `closure_claim` stays 0. -/

private theorem peelPis_constsArity {E : ResolvedEnv} :
    (n : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis n T = some (ds, r) → ConstsArity E T →
      (∀ d ∈ ds, ConstsArity E d) ∧ ConstsArity E r
  | 0, _, _, _, h, hb => by
      simp only [peelPis] at h
      injection h with h'
      injection h' with hds hr
      subst hds
      subst hr
      exact ⟨fun _ hd => absurd hd (List.not_mem_nil _), hb⟩
  | n + 1, .pi A B, _, _, h, hb => by
      simp only [peelPis] at h
      cases hp : peelPis n B with
      | none => rw [hp] at h; exact Option.noConfusion h
      | some pr =>
          rw [hp] at h
          cases pr with
          | mk ds' r' =>
              injection h with hpair
              injection hpair with hds hr
              subst hds
              subst hr
              have ⟨hds2, hr2⟩ := peelPis_constsArity n B hp hb.2
              exact ⟨fun d hd => by
                rcases List.mem_cons.mp hd with rfl | hd
                · exact hb.1
                · exact hds2 d hd, hr2⟩
  | _ + 1, .bvar _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .sort _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .const _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .app _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lam _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .letE _ _ _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h
  | _ + 1, .lit _, _, _, h, _ => by
      simp only [peelPis] at h; exact Option.noConfusion h

private theorem ConstsArity_foldr_pi {E : ResolvedEnv} {r : Expr Nat}
    (hr : ConstsArity E r) :
    (ds : List (Expr Nat)) → (∀ d ∈ ds, ConstsArity E d) →
      ConstsArity E (ds.foldr Expr.pi r)
  | [], _ => hr
  | d :: ds, hd =>
      ⟨hd d (List.mem_cons_self d ds),
        ConstsArity_foldr_pi hr ds
          (fun d' hd' => hd d' (List.mem_cons_of_mem d hd'))⟩

/-- Under `EnvWfT`, `ctorFieldTelRaw` is `ConstsArity`. -/
theorem ctorFieldTelRaw_constsArity_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) :
    ConstsArity E (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) := by
  have hC : ConstsArity E w.ctorMember.mtype :=
    hasTyT_constsArity
      (envWfT_mtypeSortTyped hW w.ctorRef w.ctorMember w.hctor).2
  have hpeel :=
    peelPis_constsArity (w.nparams + w.fields.length) w.ctorMember.mtype
      w.hpeel hC
  exact ConstsArity_foldr_pi hpeel.2 (w.ctorDoms.drop w.nparams)
    (fun d hd => hpeel.1 d (List.mem_of_mem_drop hd))

/-- `telWhnfDom` commutes with `instantiateLevels` at `ctorFieldTelRaw`.
    `EnvWfT` supplies the three premises of `telWhnfDom_instantiateLevels`.
    The parameter `instPrefix` around `ctorFieldTelInst` stays put. -/
theorem telWhnfDom_ctorFieldTelRaw_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) :
    telWhnfDom E w.fuel
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
      instantiateLevels (w.ls.take w.ctorMember.arity)
        (telWhnfDom E w.fuel
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) :=
  telWhnfDom_instantiateLevels (envWfT_levels hW)
    (envConstsArity_of_envWfT hW) (w.ls.take w.ctorMember.arity) w.fuel
    (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)
    (ctorFieldTelRaw_constsArity_of_envWfT hW w)

/-- The unconditional commute of `telWhnfDom` past parameter `instPrefix`
    is false. A `bvar` domain is already a whnf, so the right-hand side
    keeps the β-redex argument; the left-hand side reduces it. No
    `exprClosedAt`. `closure_claim` stays 0. -/
theorem telWhnfDom_instPrefix_ne :
    telWhnfDom emptyEnv 2
        (instPrefix [.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)]
          (.pi (.bvar 0) (.sort .zero))) ≠
      instPrefix [.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)]
        (telWhnfDom emptyEnv 2 (.pi (.bvar 0) (.sort .zero))) := by
  decide

/-! ## (14) `fieldsTelS` is level-blind on the stored telescope

`shapeGuardS` at `.nonrecursive` and `.recursive 0` reads Π structure and
the spine head. `instantiateLevels` changes neither
(`spineHeadConst_instantiateLevels`). A `telShapeGuarded` telescope stays
guarded, so `fieldsTelS` accepts `telWhnfDom` of the level-instantiated
`ctorFieldTelRaw`. Parameter `instPrefix` is not moved: that image is
still the walk. `closure_claim` stays 0. -/

private theorem shapeGuardS_instantiateLevels (ls : List Level) {A : Expr Nat}
    {s : FieldShape} (hNF : ∀ k, s ≠ .recursive (k + 1))
    (hg : shapeGuardS A s = true) :
    shapeGuardS (instantiateLevels ls A) s = true := by
  cases s with
  | nonrecursive => rfl
  | recursive n =>
      cases n with
      | zero =>
          simp only [shapeGuardS] at hg ⊢
          rw [spineHeadConst_instantiateLevels]
          exact hg
      | succ k => exact absurd rfl (hNF k)

private theorem telShapeGuarded_instantiateLevels {shapes : List FieldShape}
    {T : Expr Nat} (hNF : NoFunShapes shapes) (h : telShapeGuarded shapes T)
    (ls : List Level) :
    telShapeGuarded shapes (instantiateLevels ls T) := by
  induction shapes generalizing T with
  | nil => trivial
  | cons s ss ih =>
      cases T with
      | pi A B =>
          obtain ⟨hg, htail⟩ := h
          exact ⟨shapeGuardS_instantiateLevels ls
              (hNF s (List.mem_cons_self s ss)) hg,
            ih (fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')) htail⟩
      | bvar _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | sort _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | const _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | app _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | lam _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | letE _ _ _ =>
          unfold telShapeGuarded at h
          exact False.elim h
      | lit _ =>
          unfold telShapeGuarded at h
          exact False.elim h

private theorem telShapeGuarded_ctorFieldTelRaw_instLevels_of_envWfT
    {E : ResolvedEnv} (hW : EnvWfT E) (w : IotaWitnessS E)
    (hNF : NoFunShapes w.shapes) :
    telShapeGuarded w.shapes
      (telWhnfDom E w.fuel
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))) := by
  rw [telWhnfDom_ctorFieldTelRaw_of_envWfT hW w]
  exact telShapeGuarded_instantiateLevels hNF
    (telShapeGuarded_telWhnf_of_shapes w.nparams
      (w.ctorDoms.drop w.nparams) w.hshapes hNF (Nat.le_refl _))
    (w.ls.take w.ctorMember.arity)

/-- Under `EnvWfT` and `NoFunShapes`, `fieldsTelS` accepts `telWhnfDom` of
    the level-instantiated stored field telescope. The parameter
    `instPrefix` of `ctorFieldTelInst` is outside this statement. -/
theorem fieldsTelS_ctorFieldTelRaw_instLevels_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) (hNF : NoFunShapes w.shapes) :
    fieldsTelS w.fields w.shapes
      (telWhnfDom E w.fuel
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))) = true := by
  have hpeelLen : w.ctorDoms.length = w.nparams + w.fields.length :=
    peelPis_length (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hdrop : (w.ctorDoms.drop w.nparams).length = w.fields.length := by
    rw [List.length_drop, hpeelLen]
    omega
  exact fieldsTelS_of_telShapeGuarded
    (hdrop.symm.trans
      (fieldShapesFuel_length E (w.ctorDoms.drop w.nparams) w.hshapes).symm)
    hNF
    (telShapeGuarded_ctorFieldTelRaw_instLevels_of_envWfT hW w hNF)

/-! ## (15) Parameter `instPrefix` preserves the shape guard

`NoFunShapes` keeps `shapeGuardS` stable under `instantiate`
(`.recursive 0` by `spineHeadConst_instantiate`; `.nonrecursive` is
`true`). `instPrefix` is that substitution iterated, so a
`telShapeGuarded` telescope stays guarded. On the level-whnf stored
field telescope this yields `fieldsTelS` at

`instPrefix (preMajor.take nparams) (telWhnfDom fuel (instantiateLevels
(ls.take arity) ctorFieldTelRaw))`.

`telWhnfDom` remains the inner operation. The recognizer premise is
`telWhnfDom` of `ctorFieldTelInst`, which puts `instPrefix` inside.
`telWhnfDom_instPrefix_ne` is the witness that those two terms differ
when a domain is a `bvar` and an argument is a β-redex. No
`exprClosedAt`. `closure_claim` stays 0. -/

theorem telShapeGuarded_instPrefix {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes) (h : telShapeGuarded shapes T)
    (args : List (Expr Nat)) :
    telShapeGuarded shapes (instPrefix args T) := by
  induction args generalizing T with
  | nil =>
      rw [instPrefix_nil T]
      exact h
  | cons a as ih =>
      rw [instPrefix_cons a as T]
      exact ih
        (telShapeGuarded_instantiate hNF h as.length (lift 0 as.length a))

/-- Under `EnvWfT` and `NoFunShapes`, `fieldsTelS` accepts parameter
    `instPrefix` of `telWhnfDom` of the level-instantiated
    `ctorFieldTelRaw`. `telWhnfDom` is applied before `instPrefix`. -/
theorem fieldsTelS_instPrefix_ctorFieldTelRaw_instLevels_of_envWfT
    {E : ResolvedEnv} (hW : EnvWfT E) (w : IotaWitnessS E)
    (hNF : NoFunShapes w.shapes) :
    fieldsTelS w.fields w.shapes
      (instPrefix (w.preMajor.take w.nparams)
        (telWhnfDom E w.fuel
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)))) = true := by
  have hpeelLen : w.ctorDoms.length = w.nparams + w.fields.length :=
    peelPis_length (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hdrop : (w.ctorDoms.drop w.nparams).length = w.fields.length := by
    rw [List.length_drop, hpeelLen]
    omega
  exact fieldsTelS_of_telShapeGuarded
    (hdrop.symm.trans
      (fieldShapesFuel_length E (w.ctorDoms.drop w.nparams) w.hshapes).symm)
    hNF
    (telShapeGuarded_instPrefix hNF
      (telShapeGuarded_ctorFieldTelRaw_instLevels_of_envWfT hW w hNF)
      (w.preMajor.take w.nparams))

/-! ## (16) `instantiate` commutes with a const-headed whnf

`whnfFuel` reduces only the spine head. When that whnf is const-headed,
the substitute lands in the arguments and is not reduced, redex or not.
`EnvClosed` makes an unfolded δ-body ignore `instantiate`. A `bvar` head
is outside this statement: `telWhnfDom_instPrefix_ne` is that case, and
it is not claimed here. No `exprClosedAt`. `closure_claim` stays 0. -/

private theorem appsSpine_instantiate_lam (j : Nat) (v A B : Expr Nat) :
    (e : Expr Nat) → (appsSpine e).1 = .lam A B →
    appsSpine (instantiate j v e) =
      (.lam (instantiate j v A) (instantiate (j + 1) (lift 0 1 v) B),
        (appsSpine e).2.map (instantiate j v))
  | .app f x, h => by
      simp only [appsSpine] at h
      simp only [instantiate, appsSpine]
      rw [appsSpine_instantiate_lam j v A B f h]
      simp only [List.map_append, List.map_cons, List.map_nil]
  | .lam _ _, h => by
      simp only [appsSpine] at h
      cases h
      simp only [instantiate, appsSpine, List.map_nil]
  | .bvar _, h => by simp only [appsSpine] at h; nomatch h
  | .sort _, h => by simp only [appsSpine] at h; nomatch h
  | .const _ _, h => by simp only [appsSpine] at h; nomatch h
  | .pi _ _, h => by simp only [appsSpine] at h; nomatch h
  | .letE _ _ _, h => by simp only [appsSpine] at h; nomatch h
  | .lit _, h => by simp only [appsSpine] at h; nomatch h

private theorem appsSpine_instantiate_letE (j : Nat) (v A val B : Expr Nat) :
    (e : Expr Nat) → (appsSpine e).1 = .letE A val B →
    appsSpine (instantiate j v e) =
      (.letE (instantiate j v A) (instantiate j v val)
          (instantiate (j + 1) (lift 0 1 v) B),
        (appsSpine e).2.map (instantiate j v))
  | .app f x, h => by
      simp only [appsSpine] at h
      simp only [instantiate, appsSpine]
      rw [appsSpine_instantiate_letE j v A val B f h]
      simp only [List.map_append, List.map_cons, List.map_nil]
  | .letE _ _ _, h => by
      simp only [appsSpine] at h
      cases h
      simp only [instantiate, appsSpine, List.map_nil]
  | .bvar _, h => by simp only [appsSpine] at h; nomatch h
  | .sort _, h => by simp only [appsSpine] at h; nomatch h
  | .const _ _, h => by simp only [appsSpine] at h; nomatch h
  | .pi _ _, h => by simp only [appsSpine] at h; nomatch h
  | .lam _ _, h => by simp only [appsSpine] at h; nomatch h
  | .lit _, h => by simp only [appsSpine] at h; nomatch h

/-- `instantiate` commutes with `whnfFuel` when the whnf is const-headed.
    `EnvClosed` makes a δ-body ignore `instantiate`. The substitute is not
    required to be a whnf. -/
theorem whnfFuel_instantiate_of_constHead {E : ResolvedEnv}
    (hE : EnvClosed E) (j : Nat) (v : Expr Nat) :
    (fuel : Nat) → (e w : Expr Nat) →
      whnfFuel E fuel e = some w → spineHeadConst w = true →
        whnfFuel E fuel (instantiate j v e) = some (instantiate j v w)
  | 0, _, _, h, _ => by
      simp only [whnfFuel] at h
      exact Option.noConfusion h
  | fuel + 1, e, w, h, hsc => by
      simp only [whnfFuel] at h ⊢
      cases hsp : appsSpine e with
      | mk head args =>
        cases head with
        | lam A B =>
            rw [appsSpine_instantiate_lam j v A B e (by rw [hsp])]
            cases args with
            | nil =>
                simp only [hsp] at h
                injection h with hw
                subst hw
                simp only [spineHeadConst, hsp] at hsc
                nomatch hsc
            | cons x xs =>
                simp only [hsp, List.map_cons] at h ⊢
                rw [← instantiate0_instantiate, ← foldApps_instantiate]
                exact whnfFuel_instantiate_of_constHead hE j v fuel
                  (foldApps (instantiate0 x B) xs) w h hsc
        | letE A val B =>
            rw [appsSpine_instantiate_letE j v A val B e (by rw [hsp])]
            simp only [hsp] at h ⊢
            rw [← instantiate0_instantiate, ← foldApps_instantiate]
            exact whnfFuel_instantiate_of_constHead hE j v fuel
              (foldApps (instantiate0 val B) args) w h hsc
        | const r ls =>
            rw [appsSpine_instantiate_const j v r ls e (by rw [hsp])]
            simp only [hsp] at h ⊢
            cases hb : transparentBody E r ls with
            | none =>
                simp only [hb] at h ⊢
                injection h with hw
                subst hw
                rfl
            | some body =>
                simp only [hb] at h ⊢
                have hbody : instantiate j v body = body := by
                  simp only [transparentBody] at hb
                  cases hmem : E.members r with
                  | none =>
                      simp only [hmem] at hb
                      exact Option.noConfusion hb
                  | some m =>
                      simp only [hmem] at hb
                      cases htr : transparent m.mclass with
                      | false =>
                          simp only [htr] at hb
                          exact Option.noConfusion hb
                      | true =>
                          simp only [htr] at hb
                          cases hbod : m.body with
                          | none =>
                              simp only [hbod] at hb
                              exact Option.noConfusion hb
                          | some b =>
                              simp only [hbod] at hb
                              cases hb
                              exact instantiate_of_closed _
                                (instantiateLevels_closed0
                                  ((hE r m hmem).2 b hbod 0) ls) j v
                rw [← hbody, ← foldApps_instantiate]
                exact whnfFuel_instantiate_of_constHead hE j v fuel
                  (foldApps body args) w h hsc
        | bvar _ =>
            simp only [hsp] at h
            injection h with hw
            subst hw
            simp only [spineHeadConst, hsp] at hsc
            nomatch hsc
        | sort _ =>
            simp only [hsp] at h
            injection h with hw
            subst hw
            simp only [spineHeadConst, hsp] at hsc
            nomatch hsc
        | pi _ _ =>
            simp only [hsp] at h
            injection h with hw
            subst hw
            simp only [spineHeadConst, hsp] at hsc
            nomatch hsc
        | app _ _ =>
            simp only [hsp] at h
            injection h with hw
            subst hw
            simp only [spineHeadConst, hsp] at hsc
            nomatch hsc
        | lit _ =>
            simp only [hsp] at h
            injection h with hw
            subst hw
            simp only [spineHeadConst, hsp] at hsc
            nomatch hsc

/-- `instPrefix` commutes with `whnfFuel` when the whnf is const-headed.
    Each `instPrefix` step is `whnfFuel_instantiate_of_constHead`. A `bvar`
    head is outside this statement. No `exprClosedAt`. `closure_claim` stays 0. -/
theorem whnfFuel_instPrefix_of_constHead {E : ResolvedEnv}
    (hE : EnvClosed E) (fuel : Nat) (args : List (Expr Nat))
    (e w : Expr Nat) (h : whnfFuel E fuel e = some w)
    (hsc : spineHeadConst w = true) :
    whnfFuel E fuel (instPrefix args e) = some (instPrefix args w) := by
  induction args generalizing e w with
  | nil =>
      rw [instPrefix_nil, instPrefix_nil]
      exact h
  | cons a as ih =>
      rw [instPrefix_cons, instPrefix_cons]
      exact ih (instantiate as.length (lift 0 as.length a) e)
        (instantiate as.length (lift 0 as.length a) w)
        (whnfFuel_instantiate_of_constHead hE as.length (lift 0 as.length a)
          fuel e w h hsc)
        (spineHeadConst_instantiate as.length (lift 0 as.length a) w hsc)

/-! ## (17) Shape guard at `telWhnfDom` of `instPrefix`

`.nonrecursive` does not read the domain. `.recursive 0` is a
const-headed `whnfFuel`, so `whnfFuel_instantiate_of_constHead` moves
`instantiate` across that whnf. The predicate stops with the shape
list: a `bvar` tail is not a premise, and `telWhnfDom_instPrefix_ne`
stays the unconditional counterexample. No `exprClosedAt`.
`closure_claim` stays 0. -/

/-- Domains that must be const-headed for the shape guard to survive
    `telWhnfDom` after `instantiate`. `.nonrecursive` is free.
    `.recursive (k+1)` is refused. -/
def domsConstHeadFor (E : ResolvedEnv) (fuel : Nat) :
    List FieldShape → Expr Nat → Prop
  | [], _ => True
  | .nonrecursive :: ss, .pi _ B => domsConstHeadFor E fuel ss B
  | .recursive 0 :: ss, .pi A B =>
      (∃ w, whnfFuel E fuel A = some w ∧ spineHeadConst w = true) ∧
        domsConstHeadFor E fuel ss B
  | _, _ => False

private theorem pi_of_domsConstHeadFor {E : ResolvedEnv} {fuel : Nat}
    {s : FieldShape} {ss : List FieldShape} {T : Expr Nat}
    (h : domsConstHeadFor E fuel (s :: ss) T) :
    ∃ A B, T = .pi A B := by
  cases T with
  | pi A B => exact ⟨A, B, rfl⟩
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
      simp only [domsConstHeadFor] at h

private theorem domsConstHeadFor_instantiate {E : ResolvedEnv}
    (hE : EnvClosed E) {fuel : Nat} {shapes : List FieldShape} {T : Expr Nat}
    (h : domsConstHeadFor E fuel shapes T) (j : Nat) (v : Expr Nat) :
    domsConstHeadFor E fuel shapes (instantiate j v T) := by
  induction shapes generalizing T j v with
  | nil => trivial
  | cons s ss ih =>
      obtain ⟨A, B, hT⟩ := pi_of_domsConstHeadFor h
      subst hT
      cases s with
      | nonrecursive =>
          simp only [domsConstHeadFor, instantiate] at h ⊢
          exact ih h (j + 1) (lift 0 1 v)
      | recursive k =>
          cases k with
          | zero =>
              simp only [domsConstHeadFor, instantiate] at h ⊢
              obtain ⟨⟨w, hw, hsc⟩, htail⟩ := h
              exact ⟨⟨instantiate j v w,
                  whnfFuel_instantiate_of_constHead hE j v fuel A w hw hsc,
                  spineHeadConst_instantiate j v w hsc⟩,
                ih htail (j + 1) (lift 0 1 v)⟩
          | succ _ =>
              simp only [domsConstHeadFor] at h

private theorem pi_of_telShapeGuarded_cons {E : ResolvedEnv} {fuel : Nat}
    {s : FieldShape} {ss : List FieldShape} {T : Expr Nat}
    (h : telShapeGuarded (s :: ss) (telWhnfDom E fuel T)) :
    ∃ A B, T = .pi A B ∧
      shapeGuardS ((whnfFuel E fuel A).getD A) s = true ∧
      telShapeGuarded ss (telWhnfDom E fuel B) := by
  cases T with
  | pi A B =>
      refine ⟨A, B, rfl, ?_⟩
      simpa only [telWhnfDom] using h
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
      simp only [telWhnfDom, telShapeGuarded] at h

private theorem telShapeGuarded_telWhnfDom_instantiate {E : ResolvedEnv}
    (hE : EnvClosed E) {fuel : Nat} {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes)
    (hG : telShapeGuarded shapes (telWhnfDom E fuel T))
    (hD : domsConstHeadFor E fuel shapes T) (j : Nat) (v : Expr Nat) :
    telShapeGuarded shapes (telWhnfDom E fuel (instantiate j v T)) := by
  induction shapes generalizing T j v with
  | nil => trivial
  | cons s ss ih =>
      have hNF' : NoFunShapes ss :=
        fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')
      obtain ⟨A, B, hT, hg, htail⟩ := pi_of_telShapeGuarded_cons hG
      subst hT
      cases s with
      | nonrecursive =>
          simp only [domsConstHeadFor] at hD
          simp only [instantiate, telWhnfDom, telShapeGuarded]
          exact ⟨rfl, ih hNF' htail hD (j + 1) (lift 0 1 v)⟩
      | recursive k =>
          cases k with
          | zero =>
              simp only [domsConstHeadFor] at hD
              obtain ⟨⟨w, hw, hsc⟩, htailD⟩ := hD
              have hcomm :=
                whnfFuel_instantiate_of_constHead hE j v fuel A w hw hsc
              simp only [instantiate, telWhnfDom, telShapeGuarded]
              refine ⟨?_, ih hNF' htail htailD (j + 1) (lift 0 1 v)⟩
              simp only [hcomm, Option.getD_some, shapeGuardS]
              exact spineHeadConst_instantiate j v w hsc
          | succ n =>
              exact absurd rfl
                (hNF (.recursive (n + 1)) (List.mem_cons_self _ _) n)

/-- Under `EnvClosed` and `NoFunShapes`, the shape guard at `telWhnfDom`
    survives `instPrefix` when each `.recursive 0` domain has a
    const-headed whnf. `.nonrecursive` domains are unrestricted. -/
theorem telShapeGuarded_telWhnfDom_instPrefix {E : ResolvedEnv}
    (hE : EnvClosed E) {fuel : Nat} {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes)
    (hG : telShapeGuarded shapes (telWhnfDom E fuel T))
    (hD : domsConstHeadFor E fuel shapes T) (args : List (Expr Nat)) :
    telShapeGuarded shapes (telWhnfDom E fuel (instPrefix args T)) := by
  induction args generalizing T with
  | nil =>
      rw [instPrefix_nil]
      exact hG
  | cons a as ih =>
      rw [instPrefix_cons]
      exact ih
        (telShapeGuarded_telWhnfDom_instantiate hE hNF hG hD as.length
          (lift 0 as.length a))
        (domsConstHeadFor_instantiate hE hD as.length (lift 0 as.length a))

private theorem domsConstHeadFor_foldr {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices : Nat} {result : Expr Nat} (depth : Nat)
    (doms : List (Expr Nat)) {shapes : List FieldShape}
    (hsh : fieldShapesFuel E fuel fam nuniv nparams nindices depth doms = some shapes)
    (hNF : NoFunShapes shapes) (hnp : nparams ≤ depth) :
    domsConstHeadFor E fuel shapes (doms.foldr Expr.pi result) := by
  induction doms generalizing shapes depth with
  | nil =>
      simp only [fieldShapesFuel] at hsh
      injection hsh with hs
      subst hs
      trivial
  | cons T Ts ih =>
      obtain ⟨s, _, ss, ha, hr, hs⟩ := fieldShapesFuel_cons hsh
      subst hs
      have hRest : NoFunShapes ss :=
        fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')
      cases s with
      | nonrecursive =>
          simp only [domsConstHeadFor, List.foldr]
          exact ih (depth + 1) hr hRest (Nat.le_succ_of_le hnp)
      | recursive k =>
          cases k with
          | zero =>
              simp only [domsConstHeadFor, List.foldr]
              exact ⟨whnfFuel_some_const_of_recursive0 ha hnp,
                ih (depth + 1) hr hRest (Nat.le_succ_of_le hnp)⟩
          | succ j =>
              exact absurd rfl
                (hNF (.recursive (j + 1)) (List.mem_cons_self _ _) j)

private theorem domsConstHeadFor_instantiateLevels {E : ResolvedEnv}
    (hEL : EnvLevelsT E) (hEA : EnvConstsArity E) {fuel : Nat}
    {shapes : List FieldShape} {T : Expr Nat}
    (h : domsConstHeadFor E fuel shapes T) (hok : ConstsArity E T)
    (ls : List Level) :
    domsConstHeadFor E fuel shapes (instantiateLevels ls T) := by
  induction shapes generalizing T with
  | nil => trivial
  | cons s ss ih =>
      obtain ⟨A, B, hT⟩ := pi_of_domsConstHeadFor h
      subst hT
      have hB : ConstsArity E B := hok.2
      cases s with
      | nonrecursive =>
          simp only [domsConstHeadFor, instantiateLevels] at h ⊢
          exact ih h hB
      | recursive k =>
          cases k with
          | zero =>
              simp only [domsConstHeadFor, instantiateLevels] at h ⊢
              obtain ⟨⟨w, hw, hsc⟩, htail⟩ := h
              have hA : ConstsArity E A := hok.1
              have hmap := whnfFuel_instantiateLevels hEL hEA ls fuel A hA
              rw [hw] at hmap
              exact ⟨⟨instantiateLevels ls w, hmap, by
                  rw [spineHeadConst_instantiateLevels]; exact hsc⟩,
                ih htail hB⟩
          | succ _ =>
              simp only [domsConstHeadFor] at h

/-- Under `EnvWfT` and `NoFunShapes`, `fieldsTelS` accepts `telWhnfDom`
    of `ctorFieldTelInst`. `.recursive 0` domains are const-headed at the
    analysis fuel; `.nonrecursive` domains are not read. `rhsEq` is not
    this theorem. No `exprClosedAt`. `closure_claim` stays 0. -/
theorem fieldsTelS_ctorFieldTelInst_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) (hNF : NoFunShapes w.shapes) :
    fieldsTelS w.fields w.shapes
      (telWhnfDom E w.fuel (ctorFieldTelInst w)) = true := by
  have hpeelLen : w.ctorDoms.length = w.nparams + w.fields.length :=
    peelPis_length (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hdrop : (w.ctorDoms.drop w.nparams).length = w.fields.length := by
    rw [List.length_drop, hpeelLen]
    omega
  have hD : domsConstHeadFor E w.fuel w.shapes
      (instantiateLevels (w.ls.take w.ctorMember.arity)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) :=
    domsConstHeadFor_instantiateLevels (envWfT_levels hW)
      (envConstsArity_of_envWfT hW)
      (domsConstHeadFor_foldr w.nparams (w.ctorDoms.drop w.nparams) w.hshapes
        hNF (Nat.le_refl _))
      (ctorFieldTelRaw_constsArity_of_envWfT hW w)
      (w.ls.take w.ctorMember.arity)
  unfold ctorFieldTelInst
  exact fieldsTelS_of_telShapeGuarded
    (hdrop.symm.trans
      (fieldShapesFuel_length E (w.ctorDoms.drop w.nparams) w.hshapes).symm)
    hNF
    (telShapeGuarded_telWhnfDom_instPrefix (envClosed_of_envWfT hW) hNF
      (telShapeGuarded_ctorFieldTelRaw_instLevels_of_envWfT hW w hNF) hD
      (w.preMajor.take w.nparams))

/-! ## (18) Schema-lift image, without `exprClosedAt`

The schema walks `lift 0 (fl + 1 + nMinors + nindices)` of the stored
field telescope, then `instPrefix` of `preMajor ++ fields`. That suffix
is exactly the lift amount, so `instPrefix_lift` cancels it and the
image is parameter `instPrefix`. This is glm (d)'s REL₀ equation at
`ctorFieldTelInst`. It does not use `tel_cons` or `frame_shift`.
`closure_claim` stays 0. -/

/-- A suffix whose length is the lift amount does not meet `e`.
    `instPrefix (pre ++ suff) (lift 0 suff.length e)` is `instPrefix pre e`.
    No `exprClosedAt`. -/
theorem instPrefix_append_lift0 (pre suff : List (Expr Nat)) (e : Expr Nat) :
    instPrefix (pre ++ suff) (lift 0 suff.length e) = instPrefix pre e := by
  rw [instPrefix_append, instOff_lift]
  exact instPrefix_lift suff (instPrefix pre e)

/-- The schema's lifted field telescope, under `instPrefix` of
    `preMajor ++ fields`, is parameter `instPrefix` of the stored
    telescope. The suffix is `preMajor.drop nparams ++ fields`. -/
theorem instPrefix_preMajor_lift_fieldTel {E : ResolvedEnv} (w : IotaWitnessS E) :
    instPrefix (w.preMajor ++ w.fields)
        (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
          (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
      instPrefix (w.preMajor.take w.nparams)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) := by
  have hsplit :
      w.preMajor.take w.nparams ++ (w.preMajor.drop w.nparams ++ w.fields) =
        w.preMajor ++ w.fields := by
    rw [← List.append_assoc, List.take_append_drop]
  have hlen :
      (w.preMajor.drop w.nparams ++ w.fields).length =
        w.fields.length + 1 + w.nMinors + w.nindices := by
    rw [List.length_append, List.length_drop, w.hpre]
    omega
  rw [← hsplit, ← hlen]
  exact instPrefix_append_lift0 (w.preMajor.take w.nparams)
    (w.preMajor.drop w.nparams ++ w.fields)
    (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)

/-- Under `EnvWfT`, level instantiation at `w.ls` on that lifted
    telescope agrees with `ctorFieldTelInst` (`ls.take ctorMember.arity`).
    `rhsEq` is not this theorem. No `exprClosedAt`. `closure_claim` stays 0. -/
theorem ctorFieldTelInst_eq_schemaLift {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) :
    instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))) =
      ctorFieldTelInst w := by
  have hraw :=
    (lift_instantiateLevels w.ls
      (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) 0).symm
  have hsplit :
      w.preMajor.take w.nparams ++ (w.preMajor.drop w.nparams ++ w.fields) =
        w.preMajor ++ w.fields := by
    rw [← List.append_assoc, List.take_append_drop]
  have hlen :
      (w.preMajor.drop w.nparams ++ w.fields).length =
        w.fields.length + 1 + w.nMinors + w.nindices := by
    rw [List.length_append, List.length_drop, w.hpre]
    omega
  rw [hraw, ← hsplit, ← hlen, instPrefix_append_lift0]
  unfold ctorFieldTelInst
  have hlev := (envWfT_levels hW w.ctorRef w.ctorMember w.hctor).1
  have hpr := peelPis_bounded (w.nparams + w.fields.length)
    w.ctorMember.mtype w.hpeel hlev
  rw [instantiateLevels_take w.ctorMember.arity w.ls
    (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)
    (ctorFieldTelRaw_bounded hpr.1 hpr.2)]

/-! ## (19) Nonrecursive `rhsEq`

`.nonrecursive` does not read the domain. A Π-telescope of the field
count makes both walks return the field list: `iotaArgs` returns the
canonical field bvars, `rhsArgsS` returns the fields. `.recursive 0`
is not this section. No `exprClosedAt`. `closure_claim` stays 0. -/

private theorem pi_of_isPiTel_succ {n : Nat} {T : Expr Nat}
    (h : isPiTel (n + 1) T = true) :
    ∃ A B, T = .pi A B ∧ isPiTel n B = true := by
  cases T with
  | pi A B =>
      refine ⟨A, B, rfl, ?_⟩
      simpa only [isPiTel] using h
  | bvar _ => simp only [isPiTel] at h; nomatch h
  | sort _ => simp only [isPiTel] at h; nomatch h
  | const _ _ => simp only [isPiTel] at h; nomatch h
  | app _ _ => simp only [isPiTel] at h; nomatch h
  | lam _ _ => simp only [isPiTel] at h; nomatch h
  | letE _ _ _ => simp only [isPiTel] at h; nomatch h
  | lit _ => simp only [isPiTel] at h; nomatch h

theorem isPiTel_foldr (r : Expr Nat) :
    (ds : List (Expr Nat)) → isPiTel ds.length (ds.foldr Expr.pi r) = true
  | [] => rfl
  | _ :: ds => by
      simp only [List.foldr_cons, List.length_cons, isPiTel]
      exact isPiTel_foldr r ds

theorem isPiTel_telWhnfDom (E : ResolvedEnv) (fuel : Nat) :
    (n : Nat) → (T : Expr Nat) → isPiTel n T = true →
      isPiTel n (telWhnfDom E fuel T) = true
  | 0, _, _ => rfl
  | n + 1, T, h => by
      obtain ⟨A, B, hT, hB⟩ := pi_of_isPiTel_succ h
      subst hT
      simp only [telWhnfDom, isPiTel]
      exact isPiTel_telWhnfDom E fuel n B hB

theorem rhsArgsS_of_nonrec (rec : Expr Nat) (pm : List (Expr Nat))
    (np nMin : Nat) :
    (fs : List (Expr Nat)) → (ss : List FieldShape) → (T : Expr Nat) →
    (∀ s ∈ ss, s = .nonrecursive) →
    ss.length = fs.length →
    isPiTel fs.length T = true →
    rhsArgsS rec pm np nMin fs ss T = fs
  | [], [], _, _, _, _ => rfl
  | [], s :: _, _, _, hlen, _ => by
      rw [List.length_cons, List.length_nil] at hlen
      omega
  | f :: fs, [], _, _, hlen, _ => by
      rw [List.length_nil, List.length_cons] at hlen
      omega
  | f :: fs, s :: ss, T, hnr, hlen, hpi => by
      have hs : s = .nonrecursive := hnr s (List.mem_cons_self _ _)
      subst hs
      obtain ⟨A, B, hT, hB⟩ := pi_of_isPiTel_succ (by
        simpa only [List.length_cons] using hpi)
      subst hT
      have hlen' : ss.length = fs.length := by
        rw [List.length_cons, List.length_cons] at hlen
        omega
      have hnr' : ∀ s' ∈ ss, s' = .nonrecursive :=
        fun s' hs' => hnr s' (List.mem_cons_of_mem _ hs')
      simp only [rhsArgsS, recCallsS, List.nil_append]
      exact congrArg (f :: ·) (rhsArgsS_of_nonrec rec pm np nMin fs ss
        (instantiate0 f B) hnr' hlen'
        (isPiTel_instantiate 0 f fs.length B hB))

theorem iotaArgs_of_nonrec (E : ResolvedEnv) (fuel : Nat) (rec : Expr Nat)
    (pm : List (Expr Nat)) (np nMin : Nat) :
    (fs : List (Expr Nat)) → (ss : List FieldShape) → (T : Expr Nat) →
    (∀ s ∈ ss, s = .nonrecursive) →
    ss.length = fs.length →
    isPiTel fs.length T = true →
    iotaArgs E fuel rec pm np nMin ss fs T = some fs
  | [], [], _, _, _, _ => rfl
  | [], s :: _, _, _, hlen, _ => by
      rw [List.length_cons, List.length_nil] at hlen
      omega
  | f :: fs, [], _, _, hlen, _ => by
      rw [List.length_nil, List.length_cons] at hlen
      omega
  | f :: fs, s :: ss, T, hnr, hlen, hpi => by
      have hs : s = .nonrecursive := hnr s (List.mem_cons_self _ _)
      subst hs
      obtain ⟨_, B, hT, hB⟩ := pi_of_isPiTel_succ (by
        simpa only [List.length_cons] using hpi)
      subst hT
      have hlen' : ss.length = fs.length := by
        rw [List.length_cons, List.length_cons] at hlen
        omega
      have hnr' : ∀ s' ∈ ss, s' = .nonrecursive :=
        fun s' hs' => hnr s' (List.mem_cons_of_mem _ hs')
      simp only [iotaArgs]
      rw [iotaArgs_of_nonrec E fuel rec pm np nMin fs ss (instantiate0 f B)
        hnr' hlen' (isPiTel_instantiate 0 f fs.length B hB)]
      rfl

/-- Canonical field bvars under `instPrefix (preMajor ++ fields)` are the
    redex fields. This is `fieldBvars_take_map_instPrefix` at `i = nf`. -/
theorem fieldBvars_instPrefix_fields {E : ResolvedEnv} (w : IotaWitnessS E) :
    (fieldBvars w.fields.length).map (instPrefix (w.preMajor ++ w.fields)) =
      w.fields := by
  have hpm : w.preMajor.length =
      w.nparams +
        ((w.preMajor ++ w.fields).length - w.nparams - w.fields.length) := by
    rw [List.length_append, w.hpre]
    omega
  have hi : (fieldBvars w.fields.length).length ≤ w.fields.length := by
    rw [fieldBvars_length]
    exact Nat.le_refl _
  have h := fieldBvars_take_map_instPrefix
    (args := w.preMajor ++ w.fields) (pm := w.preMajor) (fs := w.fields)
    (np := w.nparams) (nf := w.fields.length)
    (i := (fieldBvars w.fields.length).length)
    rfl hpm rfl hi
  rw [List.take_length] at h
  rw [fieldBvars_length, List.take_length] at h
  exact h

/-- All-nonrecursive `rhsEq` at `telWhnfDom` of `ctorFieldTelInst`.
    `.recursive 0` is outside this statement. No `exprClosedAt`.
    `closure_claim` stays 0. -/
theorem iotaRhsOfS_eq_rhsArgsS_of_nonrec {E : ResolvedEnv} (w : IotaWitnessS E)
    (hnr : ∀ s ∈ w.shapes, s = .nonrecursive) {minor : Expr Nat}
    (hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor) :
    iotaRhsOfS w =
      foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors w.fields w.shapes
        (telWhnfDom E w.fuel (ctorFieldTelInst w))) := by
  have hpeelLen : w.ctorDoms.length = w.nparams + w.fields.length :=
    peelPis_length (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hdrop : (w.ctorDoms.drop w.nparams).length = w.fields.length := by
    rw [List.length_drop, hpeelLen]
    omega
  have hraw : isPiTel w.fields.length
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) = true := by
    rw [ctorFieldTelRaw, ← hdrop]
    exact isPiTel_foldr w.ctorResult (w.ctorDoms.drop w.nparams)
  have hsh : w.shapes.length = w.fields.length := by
    rw [fieldShapesFuel_length E (w.ctorDoms.drop w.nparams) w.hshapes, hdrop]
  have hpiL : isPiTel (fieldBvars w.fields.length).length
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
    rw [fieldBvars_length]
    exact isPiTel_lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      w.fields.length (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) hraw
  have hargs := iotaArgs_of_nonrec E w.fuel
    (.const w.recRef (canonRecLevels w.recMember.arity))
    (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
    w.nparams w.nMinors (fieldBvars w.fields.length) w.shapes
    (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))
    hnr (by rw [hsh, fieldBvars_length]) hpiL
  have hpiI : isPiTel w.fields.length (ctorFieldTelInst w) = true := by
    unfold ctorFieldTelInst
    exact isPiTel_instPrefix w.fields.length (w.preMajor.take w.nparams) _
      (by rw [isPiTel_instantiateLevels]; exact hraw)
  have hrhs := rhsArgsS_of_nonrec (.const w.recRef w.ls) w.preMajor
    w.nparams w.nMinors w.fields w.shapes
    (telWhnfDom E w.fuel (ctorFieldTelInst w)) hnr hsh
    (isPiTel_telWhnfDom E w.fuel w.fields.length (ctorFieldTelInst w) hpiI)
  have himg : (fieldBvars w.fields.length).map
      (fun a => instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
      w.fields := by
    conv =>
      rhs
      rw [← fieldBvars_instPrefix_fields w]
    apply List.map_congr_left
    intro a ha
    unfold fieldBvars at ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    rfl
  rw [iotaRhsOfS_eq_fold w hargs hm, himg, hrhs]

/-- `EnvCorrAnnDWC` when every witness is all-nonrecursive. `.recursive 0`
    is not discharged. `closure_claim` stays 0. -/
theorem envCorrAnnDWC_of_envWfT_nonrec {E : ResolvedEnv}
    (hW : EnvWfT E)
    (hnr : ∀ w : IotaWitnessS E, ∀ s ∈ w.shapes, s = .nonrecursive) :
    EnvCorrAnnDWC E := by
  refine envCorrAnnDWC_of_instPrefix_image ?_
  intro w _
  have hNF : NoFunShapes w.shapes := by
    intro s hs k heq
    have hs' : s = .nonrecursive := hnr w s hs
    subst hs'
    nomatch heq
  refine ⟨fieldsTelS_ctorFieldTelInst_of_envWfT hW w hNF, ?_⟩
  intro minor hm
  exact iotaRhsOfS_eq_rhsArgsS_of_nonrec w (hnr w) hm

/-! ## (20) `.recursive 0` — one `whnfFuel` step is an empty `piTelescopeFuel`

`iotaArgs` inserts `recCallField` on the body `piTelescopeFuel` returns.
A non-Π whnf is that empty telescope. `.recursive (k+1)` is not this
step. `closure_claim` stays 0. -/

theorem piTelescopeFuel_nil_of_whnf {E : ResolvedEnv} {fuel : Nat}
    {e w : Expr Nat} (hw : whnfFuel E fuel e = some w)
    (hpi : ∀ A B, w ≠ .pi A B) :
    piTelescopeFuel E (fuel + 1) e = some ([], w) := by
  unfold piTelescopeFuel
  rw [hw]
  cases w with
  | pi A B => exact absurd rfl (hpi A B)
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ => rfl
  | lam _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

theorem iotaArgs_recursive0_of_nil {E : ResolvedEnv} (fuel : Nat)
    (rec : Expr Nat) (preMajor : List (Expr Nat)) (nparams nMinors : Nat)
    (ss : List FieldShape) (f : Expr Nat) (fs : List (Expr Nat))
    (A B famApp : Expr Nat) (rest : List (Expr Nat))
    (hpt : piTelescopeFuel E fuel A = some ([], famApp))
    (hrest : iotaArgs E fuel rec preMajor nparams nMinors ss fs
        (instantiate0 f B) = some rest) :
    iotaArgs E fuel rec preMajor nparams nMinors
        (.recursive 0 :: ss) (f :: fs) (.pi A B) =
      some (f :: recCallField rec preMajor nparams nMinors f famApp :: rest) := by
  unfold iotaArgs
  rw [hpt, hrest]
  rfl

/-- `.recursive 0` at the witness fuel is `piTelescopeFuel` of an empty
    telescope. The classifier reads one fuel lower; `whnfFuel_mono` and
    `piTelescopeFuel_nil_of_whnf` raise it. `.recursive (k+1)` is not this
    statement. `closure_claim` stays 0. -/
theorem piTelescopeFuel_of_recursive0 {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth T =
      .permitted (.recursive 0) idx)
    (hnp : nparams ≤ depth) :
    ∃ body, piTelescopeFuel E fuel T = some ([], body) ∧
      idx = familyIdx nparams body ∧ spineHeadConst body = true := by
  obtain ⟨doms, body, hpt, hlen, hidx, hproper⟩ := fieldAnalyze_recursive_out h
  have hnpt : nparams ≤ (doms.length + depth - 1) + 1 := by
    rw [hlen]
    omega
  obtain ⟨ls, args, hbody, _, _, _⟩ := properFamilyFuel_true hnpt hproper
  have hnil : doms = [] := by
    cases doms with
    | nil => rfl
    | cons _ _ =>
        rw [List.length_cons] at hlen
        exact absurd hlen (Nat.succ_ne_zero _)
  subst hnil
  obtain ⟨f, hf, hw⟩ := piTel_nil_whnf E hpt
  have hwUp : whnfFuel E (fuel - 1) T = some body := by
    rw [hf]
    exact whnfFuel_mono E (Nat.le_succ f) hw
  have hpi : ∀ A B, body ≠ .pi A B := by
    intro A B hb
    rw [hbody] at hb
    have hsp := appsSpine_foldApps_const fam ls args
    rw [hb] at hsp
    simp only [appsSpine] at hsp
    exact Expr.noConfusion (congrArg Prod.fst hsp)
  have htel := piTelescopeFuel_nil_of_whnf hwUp hpi
  have hfuel : (fuel - 1) + 1 = fuel := by
    rw [hf]
    omega
  have hsc : spineHeadConst body = true := by
    rw [hbody]
    unfold spineHeadConst
    rw [appsSpine_foldApps_const]
  refine ⟨body, ?_, hidx, hsc⟩
  rw [← hfuel]
  exact htel

/-- `rhsArgsS` at `.recursive 0` inserts `recCallField` on the domain
    itself. The `iotaArgs` side uses the `piTelescopeFuel` body
    (`iotaArgs_recursive0_of_nil`). `.recursive (k+1)` is not this
    equation. `closure_claim` stays 0. -/
theorem rhsArgsS_recursive0 (rec : Expr Nat) (pre : List (Expr Nat))
    (nparams nMinors : Nat) (f : Expr Nat) (fs : List (Expr Nat))
    (A B : Expr Nat) (ss : List FieldShape) :
    rhsArgsS rec pre nparams nMinors (f :: fs) (.recursive 0 :: ss) (.pi A B) =
      f :: recCallField rec pre nparams nMinors f A ::
        rhsArgsS rec pre nparams nMinors fs ss (instantiate0 f B) := by
  simp only [rhsArgsS, recCallsS, List.singleton_append]

/-- Schema-side `recCallField` at canonical levels and `preMajorBvars`,
    imaged by `instPrefix (preMajor ++ fields)` after `instantiateLevels`.
    The recursor head is `canonRecLevels_instLevel`. The prelude is
    `preMajorBvars_map_instPrefix`. The field and the family indices stay
    hypotheses. This is not `recCallField_img`. `closure_claim` stays 0. -/
theorem recCallField_schemaImg {E : ResolvedEnv} (w : IotaWitnessS E)
    (fcan fr A_C A_R : Expr Nat)
    (hf : instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls fcan) = fr)
    (hidx : (familyIdx w.nparams (instantiateLevels w.ls A_C)).map
        (instPrefix (w.preMajor ++ w.fields)) = familyIdx w.nparams A_R) :
    instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls
          (recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors fcan A_C)) =
      recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors fr A_R := by
  rw [recCallField_instLevels]
  have hhead := instantiateLevels_const_canonRecLevels w.ls w.recRef
    w.recMember.arity w.hlsLen
  have hbvs :
      (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length).map
        (instantiateLevels w.ls) =
      preMajorBvars w.nparams w.nMinors w.nindices w.fields.length := by
    unfold preMajorBvars
    exact map_instantiateLevels_bvars w.ls (fun i => i + w.fields.length)
      ((List.range (w.nparams + 1 + w.nMinors + w.nindices)).reverse)
  unfold recCallField
  rw [instPrefix_foldApps, hhead, instPrefix_const]
  apply congrArg (foldApps (.const w.recRef w.ls))
  rw [List.map_append, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [hf, hidx]
  have hpre :
      (recPrefix
          ((preMajorBvars w.nparams w.nMinors w.nindices w.fields.length).map
            (instantiateLevels w.ls))
          w.nparams w.nMinors).map
        (instPrefix (w.preMajor ++ w.fields)) =
      recPrefix w.preMajor w.nparams w.nMinors := by
    rw [hbvs]
    have hall := preMajorBvars_map_instPrefix w.preMajor w.fields
      w.nparams w.nMinors w.nindices w.hpre
    unfold recPrefix
    rw [List.map_take, hall]
  rw [hpre]

/-- A field bvar, after `instantiateLevels`, is the redex field at the
    reversed index. This is `instPrefix_append_fieldBvar`. It discharges
    the field hypothesis of `recCallField_schemaImg`. `closure_claim` stays 0. -/
theorem fieldBvar_schemaImg {pre fields : List (Expr Nat)} (ls : List Level)
    {k : Nat} {a : Expr Nat} (hk : k < fields.length)
    (hget : fields[fields.length - 1 - k]? = some a) :
    instPrefix (pre ++ fields) (instantiateLevels ls (.bvar k)) = a := by
  rw [show instantiateLevels ls (.bvar k) = .bvar k from rfl]
  exact instPrefix_append_fieldBvar hk hget

/-- `familyIdx` commutes with `instPrefix` on a const-headed spine.
    One `instantiate` step is `familyIdx_instantiate_const`. This is the
    index half of a `.recursive 0` image, before the domain itself is
    identified. `closure_claim` stays 0. -/
theorem familyIdx_instPrefix_const (args : List (Expr Nat)) (nparams : Nat)
    {r : Nat} {ls : List Level} {A : Expr Nat}
    (h : (appsSpine A).1 = .const r ls) :
    familyIdx nparams (instPrefix args A) =
      (familyIdx nparams A).map (instPrefix args) := by
  induction args generalizing A with
  | nil =>
      simp only [instPrefix]
      exact (List.map_id (familyIdx nparams A)).symm
  | cons a as ih =>
      rw [instPrefix_cons]
      have hsp := appsSpine_instantiate_const as.length
        (lift 0 as.length a) r ls A h
      have hhead : (appsSpine (instantiate as.length (lift 0 as.length a) A)).1 =
          .const r ls := by
        rw [hsp]
      rw [ih hhead, familyIdx_instantiate_const as.length
        (lift 0 as.length a) nparams h, List.map_map]
      rfl

/-! ## (21) Schema-domain whnf image

The whnf of `instPrefix` after `instantiateLevels` is the image of the
schema whnf, when that whnf is const-headed. This is
`whnfFuel_instantiateLevels` then `whnfFuel_instPrefix_of_constHead`.
`familyIdx_instPrefix_const` then discharges the index hypothesis of
`recCallField_schemaImg`. The field hypothesis stays
`fieldBvar_schemaImg`. A `bvar` head is outside this section
(`telWhnfDom_instPrefix_ne`). `.recursive (k+1)` is not these names.
`envCorrAnnDWC_of_envWfT` is not claimed. No `exprClosedAt`.
`closure_claim` stays 0. -/

/-- `whnfFuel` commutes with `instPrefix` of `instantiateLevels` when
    the whnf is const-headed. The level step is
    `whnfFuel_instantiateLevels`; the prefix step is
    `whnfFuel_instPrefix_of_constHead`. -/
theorem whnfFuel_schemaDom {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (ls : List Level) (args : List (Expr Nat)) (fuel : Nat)
    (A w : Expr Nat) (hok : ConstsArity E A)
    (hw : whnfFuel E fuel A = some w)
    (hsc : spineHeadConst w = true) :
    whnfFuel E fuel (instPrefix args (instantiateLevels ls A)) =
      some (instPrefix args (instantiateLevels ls w)) := by
  have hL : whnfFuel E fuel (instantiateLevels ls A) =
      some (instantiateLevels ls w) := by
    rw [whnfFuel_instantiateLevels hEL hEA ls fuel A hok, hw]
    rfl
  have hscL : spineHeadConst (instantiateLevels ls w) = true := by
    rw [spineHeadConst_instantiateLevels]
    exact hsc
  exact whnfFuel_instPrefix_of_constHead hE fuel args
    (instantiateLevels ls A) (instantiateLevels ls w) hL hscL

/-- The domain `telWhnfDom` reads is that image. `getD` of the `some`
    whnf is `instPrefix` of `instantiateLevels` on the schema body. -/
theorem schemaDom_whnf {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (ls : List Level) (args : List (Expr Nat)) (fuel : Nat)
    (A w : Expr Nat) (hok : ConstsArity E A)
    (hw : whnfFuel E fuel A = some w)
    (hsc : spineHeadConst w = true) :
    (whnfFuel E fuel (instPrefix args (instantiateLevels ls A))).getD
        (instPrefix args (instantiateLevels ls A)) =
      instPrefix args (instantiateLevels ls w) := by
  rw [whnfFuel_schemaDom hE hEL hEA ls args fuel A w hok hw hsc]
  rfl

/-- `familyIdx_instPrefix_const` on a level-instantiated const spine.
    This is the index hypothesis of `recCallField_schemaImg` at
    `A_R = instPrefix args (instantiateLevels ls A)`. -/
theorem familyIdx_schemaBody (args : List (Expr Nat)) (nparams : Nat)
    (ls : List Level) {r : Nat} {us : List Level} {A : Expr Nat}
    (h : (appsSpine A).1 = .const r us) :
    (familyIdx nparams (instantiateLevels ls A)).map (instPrefix args) =
      familyIdx nparams (instPrefix args (instantiateLevels ls A)) := by
  have hhead : (appsSpine (instantiateLevels ls A)).1 =
      .const r (us.map (instLevel ls)) := by
    rw [appsSpine_instantiateLevels, h]
    rfl
  exact (familyIdx_instPrefix_const args nparams hhead).symm

/-- The index hypothesis of `recCallField_schemaImg` is
    `familyIdx_schemaBody` when the schema body is const-headed.
    The right-hand domain is the image of that body. The field
    hypothesis stays. This is not `recCallField_img`. -/
theorem recCallField_schemaImg_const {E : ResolvedEnv} (w : IotaWitnessS E)
    (fcan fr A_C : Expr Nat) {r : Nat} {us : List Level}
    (hf : instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls fcan) = fr)
    (h : (appsSpine A_C).1 = .const r us) :
    instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls
          (recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors fcan A_C)) =
      recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors fr
        (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A_C)) := by
  exact recCallField_schemaImg w fcan fr A_C
    (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A_C))
    hf (familyIdx_schemaBody (w.preMajor ++ w.fields) w.nparams w.ls h)

/-- The schema `recCallField` on the whnf body agrees with `recCallField`
    on the whnf of the instantiated domain. The index step is
    `recCallField_schemaImg_const`. The domain step is `schemaDom_whnf`. -/
theorem recCallField_schemaWhnf {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (w : IotaWitnessS E) (fcan fr A body : Expr Nat)
    {r : Nat} {us : List Level}
    (hok : ConstsArity E A)
    (hw : whnfFuel E w.fuel A = some body)
    (h : (appsSpine body).1 = .const r us)
    (hf : instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls fcan) = fr) :
    instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls
          (recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors fcan body)) =
      recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors fr
        ((whnfFuel E w.fuel
            (instPrefix (w.preMajor ++ w.fields)
              (instantiateLevels w.ls A))).getD
          (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A))) := by
  have hsc : spineHeadConst body = true := by
    unfold spineHeadConst
    rw [h]
  rw [schemaDom_whnf hE hEL hEA w.ls (w.preMajor ++ w.fields) w.fuel
    A body hok hw hsc]
  exact recCallField_schemaImg_const w fcan fr body hf h

/-! ## (22) One `.recursive 0` argument cons

The schema list is the field, then `recCallField` on the whnf body,
then the tail. `instPrefix` of `instantiateLevels` sends that cons to
the list `rhsArgsS` inserts on the whnf domain. `take 2` drops the
tail, so this step does not use `instPrefix_step`. The tail image
stays a `map`. `.recursive (k+1)` is not this section.
`envCorrAnnDWC_of_envWfT` is not claimed. No `exprClosedAt`.
`closure_claim` stays 0. -/

/-- The image of a `.recursive 0` cons. The call is
    `recCallField_schemaWhnf`. The tail stays under `map`. -/
theorem recursive0_argsImg {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (w : IotaWitnessS E) (fcan fr A body : Expr Nat)
    (rest : List (Expr Nat)) {r : Nat} {us : List Level}
    (hok : ConstsArity E A)
    (hw : whnfFuel E w.fuel A = some body)
    (h : (appsSpine body).1 = .const r us)
    (hf : instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls fcan) = fr) :
    (fcan ::
        recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors fcan body :: rest).map
      (fun a => instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
    fr ::
      recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors fr
        ((whnfFuel E w.fuel
            (instPrefix (w.preMajor ++ w.fields)
              (instantiateLevels w.ls A))).getD
          (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A))) ::
      rest.map (fun a =>
        instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) := by
  simp only [List.map_cons]
  rw [hf, recCallField_schemaWhnf hE hEL hEA w fcan fr A body hok hw h hf]

/-- `take 2` of that image is `take 2` of `rhsArgsS` at `.recursive 0`
    on the whnf domain. The tail of `rhsArgsS` is not read. -/
theorem recursive0_headImg {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (w : IotaWitnessS E) (fcan fr A body B : Expr Nat)
    (fs : List (Expr Nat)) (ss : List FieldShape) (rest : List (Expr Nat))
    {r : Nat} {us : List Level}
    (hok : ConstsArity E A)
    (hw : whnfFuel E w.fuel A = some body)
    (h : (appsSpine body).1 = .const r us)
    (hf : instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls fcan) = fr) :
    ((fcan ::
        recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors fcan body :: rest).map
      (fun a => instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a))).take 2 =
    (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      (fr :: fs) (.recursive 0 :: ss)
      (.pi ((whnfFuel E w.fuel
          (instPrefix (w.preMajor ++ w.fields)
            (instantiateLevels w.ls A))).getD
        (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A))) B)).take 2 := by
  rw [recursive0_argsImg hE hEL hEA w fcan fr A body rest hok hw h hf,
    rhsArgsS_recursive0]
  rfl

/-! ## (23) The body of one `.recursive 0` step

`recursive0_headImg` equates `take 2`. The continuation is `instantiate0`
on the telescope body. `instPrefix` of `instantiateLevels` on
`instantiate0` of a field bvar is `instantiate0` of that bvar's image
into `instTel` of the level image. `instTel` is the body `instPrefix_pi`
already names. `instOff 1` is that body. This is not `instPrefix_step`.
`.recursive (k+1)` is not this section. `envCorrAnnDWC_of_envWfT` is
not claimed. No `exprClosedAt`. `closure_claim` stays 0. -/

/-- `instOff 1` is `instTel`. The index `1 + n` is `n + 1`. -/
theorem instOff_one_instTel (xs : List (Expr Nat)) (e : Expr Nat) :
    instOff 1 xs e = instTel xs e := by
  induction xs generalizing e with
  | nil => rfl
  | cons a as ih =>
      rw [instOff_cons, instTel_cons]
      have hidx : 1 + as.length = as.length + 1 := by omega
      rw [hidx]
      exact ih _

private theorem instPrefix_instantiate0_bvar (X : List (Expr Nat)) (k : Nat)
    (e : Expr Nat) :
    instPrefix X (instantiate0 (.bvar k) e) =
      instantiate0 (instPrefix X (.bvar k)) (instTel X e) := by
  have h1 : instPrefix [.bvar k] e = instantiate0 (.bvar k) e := by
    rw [instPrefix_cons, List.length_nil, lift_zero_idx, instPrefix_nil]
    unfold instantiate0
    rfl
  rw [← h1, instPrefix_instPrefix X [.bvar k] e, List.map_cons, List.map_nil,
    instPrefix_append X [instPrefix X (.bvar k)] e, List.length_singleton,
    instOff_one_instTel, instPrefix_cons, List.length_nil, lift_zero_idx,
    instPrefix_nil]
  unfold instantiate0
  rfl

/-- The image of `instantiate0` on a field bvar is `instantiate0` of the
    bvar's image into `instTel` of the level image. The level step is
    `instantiateLevels_instantiate0`. The prefix step is
    `instPrefix_instantiate0_bvar`. Not `instPrefix_step`. -/
theorem recursive0_bodyImg (X : List (Expr Nat)) (k : Nat) (ls : List Level)
    (B : Expr Nat) :
    instPrefix X (instantiateLevels ls (instantiate0 (.bvar k) B)) =
      instantiate0 (instPrefix X (.bvar k))
        (instTel X (instantiateLevels ls B)) := by
  rw [instantiateLevels_instantiate0]
  exact instPrefix_instantiate0_bvar X k (instantiateLevels ls B)

/-- `rhsArgsS` at `.recursive 0` continues on `instantiate0` of the
    telescope body. When that body is `instTel` of the level image, the
    continuation subject is the image of `instantiate0` on the schema
    body. The domain is the whnf domain the caller passes. The head is
    `rhsArgsS_recursive0`. Not `instPrefix_step`. -/
theorem recursive0_tailImg (rec : Expr Nat) (pre : List (Expr Nat))
    (nparams nMinors : Nat) (X : List (Expr Nat)) (k : Nat)
    (ls : List Level) (fr dom : Expr Nat) (fs : List (Expr Nat))
    (ss : List FieldShape) (B : Expr Nat)
    (hf : instPrefix X (.bvar k) = fr) :
    rhsArgsS rec pre nparams nMinors (fr :: fs) (.recursive 0 :: ss)
        (.pi dom (instTel X (instantiateLevels ls B))) =
      fr :: recCallField rec pre nparams nMinors fr dom ::
        rhsArgsS rec pre nparams nMinors fs ss
          (instPrefix X (instantiateLevels ls (instantiate0 (.bvar k) B))) := by
  rw [rhsArgsS_recursive0, recursive0_bodyImg X k ls B, hf]

/-- One `.recursive 0` step, given the tail. The head is
    `recursive0_argsImg`. The continuation subject is
    `recursive0_tailImg`. The tail list stays a hypothesis. This is
    not the mixed induction, and not `instPrefix_step`. -/
theorem recursive0_stepImg {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (w : IotaWitnessS E) (k : Nat) (fr A body B : Expr Nat)
    (rest fs : List (Expr Nat)) (ss : List FieldShape)
    {r : Nat} {us : List Level}
    (hok : ConstsArity E A)
    (hw : whnfFuel E w.fuel A = some body)
    (hsp : (appsSpine body).1 = .const r us)
    (hf : instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls (.bvar k)) = fr)
    (htail : rest.map (fun a =>
        instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
      rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        fs ss
        (instPrefix (w.preMajor ++ w.fields)
          (instantiateLevels w.ls (instantiate0 (.bvar k) B)))) :
    ((.bvar k ::
        recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors (.bvar k) body :: rest).map
      (fun a => instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls a))) =
    rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      (fr :: fs) (.recursive 0 :: ss)
      (.pi ((whnfFuel E w.fuel
          (instPrefix (w.preMajor ++ w.fields)
            (instantiateLevels w.ls A))).getD
        (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A)))
        (instTel (w.preMajor ++ w.fields) (instantiateLevels w.ls B))) := by
  rw [recursive0_argsImg hE hEL hEA w (.bvar k) fr A body rest hok hw hsp hf,
    recursive0_tailImg (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      (w.preMajor ++ w.fields) k w.ls fr
      ((whnfFuel E w.fuel
          (instPrefix (w.preMajor ++ w.fields)
            (instantiateLevels w.ls A))).getD
        (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls A)))
      fs ss B hf, htail]

/-! ## (24) `rhsArgsS` when `telWhnfDom` crosses `instantiate`

The redex walk starts at `telWhnfDom`, so its continuation is
`instantiate0` on `telWhnfDom` of the body. The schema image of that
continuation is `telWhnfDom` of `instantiate0` (`recursive0_bodyImg`).
Those subjects are not the same expression: a `.nonrecursive` domain
may be a `bvar`, and `telWhnfDom_instPrefix_ne` is that witness.
`.recursive 0` domains are const-headed, so
`whnfFuel_instantiate_of_constHead` makes the domain `rhsArgsS` reads
agree, and a `.nonrecursive` domain is not read. Not the mixed
induction. Not `instPrefix_step`. Not `envCorrAnnDWC_of_envWfT`.
No `exprClosedAt`. `closure_claim` stays 0. -/

/-- What `rhsArgsS` reads. `.recursive 0` shares the domain expression.
    `.nonrecursive` does not. `.recursive (k+1)` is not a constructor. -/
inductive RhsTelRel : List FieldShape → Expr Nat → Expr Nat → Prop where
  | nil {L R : Expr Nat} : RhsTelRel [] L R
  | nrec {ss : List FieldShape} {AL BL AR BR : Expr Nat}
      (h : RhsTelRel ss BL BR) :
      RhsTelRel (.nonrecursive :: ss) (.pi AL BL) (.pi AR BR)
  | rec0 {ss : List FieldShape} {A BL BR : Expr Nat}
      (h : RhsTelRel ss BL BR) :
      RhsTelRel (.recursive 0 :: ss) (.pi A BL) (.pi A BR)

theorem RhsTelRel.instantiate {shapes : List FieldShape} {L R : Expr Nat}
    (h : RhsTelRel shapes L R) (j : Nat) (v : Expr Nat) :
    RhsTelRel shapes (instantiate j v L) (instantiate j v R) := by
  induction h generalizing j v with
  | nil => exact RhsTelRel.nil
  | nrec _ ih =>
      exact RhsTelRel.nrec (ih (j + 1) (lift 0 1 v))
  | rec0 _ ih =>
      exact RhsTelRel.rec0 (ih (j + 1) (lift 0 1 v))

theorem rhsArgsS_of_RhsTelRel (rec : Expr Nat) (pre : List (Expr Nat))
    (nparams nMinors : Nat) {shapes : List FieldShape} {L R : Expr Nat}
    (fs : List (Expr Nat)) (h : RhsTelRel shapes L R) :
    rhsArgsS rec pre nparams nMinors fs shapes L =
      rhsArgsS rec pre nparams nMinors fs shapes R := by
  induction shapes generalizing L R fs with
  | nil =>
      cases h
      cases fs <;> rfl
  | cons _ ss ih =>
      cases h with
      | nrec htail =>
          cases fs with
          | nil => rfl
          | cons f fs =>
              simp only [rhsArgsS, recCallsS, List.nil_append]
              exact congrArg (f :: ·)
                (ih fs (RhsTelRel.instantiate htail 0 f))
      | rec0 htail =>
          cases fs with
          | nil => rfl
          | cons f fs =>
              simp only [rhsArgsS, recCallsS, List.singleton_append]
              exact congrArg
                (fun t =>
                  f :: recCallField rec pre nparams nMinors f _ :: t)
                (ih fs (RhsTelRel.instantiate htail 0 f))

theorem rhsTelRel_telWhnfDom_instantiate {E : ResolvedEnv}
    (hE : EnvClosed E) {fuel : Nat} {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes) (hD : domsConstHeadFor E fuel shapes T)
    (j : Nat) (v : Expr Nat) :
    RhsTelRel shapes (telWhnfDom E fuel (instantiate j v T))
      (instantiate j v (telWhnfDom E fuel T)) := by
  induction shapes generalizing T j v with
  | nil => exact RhsTelRel.nil
  | cons s ss ih =>
      obtain ⟨A, B, rfl⟩ := pi_of_domsConstHeadFor hD
      have hNF' : NoFunShapes ss :=
        fun s' hs' => hNF s' (List.mem_cons_of_mem s hs')
      cases s with
      | nonrecursive =>
          simp only [domsConstHeadFor] at hD
          exact RhsTelRel.nrec (ih hNF' hD (j + 1) (lift 0 1 v))
      | recursive k =>
          cases k with
          | zero =>
              simp only [domsConstHeadFor] at hD
              obtain ⟨⟨w, hw, hsc⟩, htail⟩ := hD
              have hdom :
                  (whnfFuel E fuel (instantiate j v A)).getD
                      (instantiate j v A) =
                    instantiate j v ((whnfFuel E fuel A).getD A) := by
                rw [whnfFuel_instantiate_of_constHead hE j v fuel A w hw hsc,
                  hw]
                rfl
              simp only [telWhnfDom, instantiate]
              rw [hdom]
              exact RhsTelRel.rec0 (ih hNF' htail (j + 1) (lift 0 1 v))
          | succ n =>
              exact absurd rfl
                (hNF (.recursive (n + 1)) (List.mem_cons_self _ _) n)

theorem rhsArgsS_telWhnfDom_instantiate {E : ResolvedEnv}
    (hE : EnvClosed E) (rec : Expr Nat) (pre : List (Expr Nat))
    (nparams nMinors fuel : Nat) (fs : List (Expr Nat))
    {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes) (hD : domsConstHeadFor E fuel shapes T)
    (j : Nat) (v : Expr Nat) :
    rhsArgsS rec pre nparams nMinors fs shapes
        (telWhnfDom E fuel (instantiate j v T)) =
      rhsArgsS rec pre nparams nMinors fs shapes
        (instantiate j v (telWhnfDom E fuel T)) :=
  rhsArgsS_of_RhsTelRel rec pre nparams nMinors fs
    (rhsTelRel_telWhnfDom_instantiate hE hNF hD j v)

/-- The two continuation subjects of one walk step. The redex side is
    `instantiate0` on `telWhnfDom`. The image side is `telWhnfDom` on
    `instantiate0`. `rhsArgsS_telWhnfDom_instantiate` at index 0. -/
theorem rhsArgsS_instantiate0_telWhnfDom {E : ResolvedEnv}
    (hE : EnvClosed E) (rec : Expr Nat) (pre : List (Expr Nat))
    (nparams nMinors fuel : Nat) (f : Expr Nat) (fs : List (Expr Nat))
    {shapes : List FieldShape} {T : Expr Nat}
    (hNF : NoFunShapes shapes) (hD : domsConstHeadFor E fuel shapes T) :
    rhsArgsS rec pre nparams nMinors fs shapes
        (instantiate0 f (telWhnfDom E fuel T)) =
      rhsArgsS rec pre nparams nMinors fs shapes
        (telWhnfDom E fuel (instantiate0 f T)) :=
  (rhsArgsS_telWhnfDom_instantiate hE rec pre nparams nMinors fuel fs hNF hD
      0 f).symm

/-! ## (25) One `.recursive 0` step at `telWhnfDom`

`recursive0_stepImg` continues on the raw `instantiate0` of `instTel`.
The recognizer continues on `instantiate0` of `telWhnfDom` of that body.
`rhsArgsS_instantiate0_telWhnfDom` equates those walks. The tail stays
a hypothesis. Not the mixed induction. Not `instPrefix_step`.
Not `envCorrAnnDWC_of_envWfT`. No `exprClosedAt`. `closure_claim` stays 0. -/

/-- One `.recursive 0` cons at `telWhnfDom` of the level image, given
    the tail at `telWhnfDom` of the instantiated body. The head is
    `recursive0_argsImg`. The continuation crosses `telWhnfDom` by
    `rhsArgsS_instantiate0_telWhnfDom`. -/
theorem recursive0_stepWhnf {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (w : IotaWitnessS E) (k : Nat) (fr A body B : Expr Nat)
    (rest fs : List (Expr Nat)) (ss : List FieldShape)
    {r : Nat} {us : List Level}
    (hok : ConstsArity E A)
    (hw : whnfFuel E w.fuel A = some body)
    (hsp : (appsSpine body).1 = .const r us)
    (hf : instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls (.bvar k)) = fr)
    (hNF : NoFunShapes ss)
    (hD : domsConstHeadFor E w.fuel ss
      (instTel (w.preMajor ++ w.fields) (instantiateLevels w.ls B)))
    (htail : rest.map (fun a =>
        instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
      rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        fs ss
        (telWhnfDom E w.fuel
          (instPrefix (w.preMajor ++ w.fields)
            (instantiateLevels w.ls (instantiate0 (.bvar k) B))))) :
    ((.bvar k ::
        recCallField (.const w.recRef (canonRecLevels w.recMember.arity))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors (.bvar k) body :: rest).map
      (fun a => instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls a))) =
    rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      (fr :: fs) (.recursive 0 :: ss)
      (telWhnfDom E w.fuel
        (instPrefix (w.preMajor ++ w.fields)
          (instantiateLevels w.ls (.pi A B)))) := by
  rw [recursive0_argsImg hE hEL hEA w (.bvar k) fr A body rest hok hw hsp hf]
  have hLev :
      instantiateLevels w.ls (.pi A B) =
        .pi (instantiateLevels w.ls A) (instantiateLevels w.ls B) := rfl
  rw [hLev, instPrefix_pi (w.preMajor ++ w.fields)]
  simp only [telWhnfDom, rhsArgsS, recCallsS, List.singleton_append]
  refine congrArg
      (fun t =>
        fr ::
          recCallField (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors fr
            ((whnfFuel E w.fuel
                (instPrefix (w.preMajor ++ w.fields)
                  (instantiateLevels w.ls A))).getD
              (instPrefix (w.preMajor ++ w.fields)
                (instantiateLevels w.ls A))) ::
          t)
      ?_
  have hbody := recursive0_bodyImg (w.preMajor ++ w.fields) k w.ls B
  have hbv :
      instPrefix (w.preMajor ++ w.fields) (.bvar k) = fr := by
    simpa only [instantiateLevels] using hf
  rw [hbv] at hbody
  rw [hbody] at htail
  have hwalk :=
    rhsArgsS_instantiate0_telWhnfDom hE (.const w.recRef w.ls) w.preMajor
      w.nparams w.nMinors w.fuel fr fs hNF hD
  rw [← hwalk] at htail
  exact htail

/-! ## (26) One `.nonrecursive` step at `telWhnfDom`

`.nonrecursive` does not read the domain and does not insert
`recCallField`. The continuation is the same walk as
`recursive0_stepWhnf`: `rhsArgsS` on `telWhnfDom` of the instantiated
body, moved by `rhsArgsS_instantiate0_telWhnfDom`. Not the mixed
induction. Not `instPrefix_step`. Not `envCorrAnnDWC_of_envWfT`.
No `exprClosedAt`. `closure_claim` stays 0. -/

/-- One `.nonrecursive` cons at `telWhnfDom` of the level image, given
    the tail at `telWhnfDom` of the instantiated body. The domain is
    not read. -/
theorem nonrecursive_stepWhnf {E : ResolvedEnv}
    (hE : EnvClosed E) (w : IotaWitnessS E) (k : Nat) (fr A B : Expr Nat)
    (rest fs : List (Expr Nat)) (ss : List FieldShape)
    (hf : instPrefix (w.preMajor ++ w.fields)
        (instantiateLevels w.ls (.bvar k)) = fr)
    (hNF : NoFunShapes ss)
    (hD : domsConstHeadFor E w.fuel ss
      (instTel (w.preMajor ++ w.fields) (instantiateLevels w.ls B)))
    (htail : rest.map (fun a =>
        instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
      rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        fs ss
        (telWhnfDom E w.fuel
          (instPrefix (w.preMajor ++ w.fields)
            (instantiateLevels w.ls (instantiate0 (.bvar k) B))))) :
    ((.bvar k :: rest).map (fun a =>
        instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a))) =
    rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      (fr :: fs) (.nonrecursive :: ss)
      (telWhnfDom E w.fuel
        (instPrefix (w.preMajor ++ w.fields)
          (instantiateLevels w.ls (.pi A B)))) := by
  simp only [List.map_cons, hf]
  have hLev :
      instantiateLevels w.ls (.pi A B) =
        .pi (instantiateLevels w.ls A) (instantiateLevels w.ls B) := rfl
  rw [hLev, instPrefix_pi (w.preMajor ++ w.fields)]
  simp only [telWhnfDom, rhsArgsS, recCallsS, List.nil_append]
  refine congrArg (fr :: ·) ?_
  have hbody := recursive0_bodyImg (w.preMajor ++ w.fields) k w.ls B
  have hbv :
      instPrefix (w.preMajor ++ w.fields) (.bvar k) = fr := by
    simpa only [instantiateLevels] using hf
  rw [hbv] at hbody
  rw [hbody] at htail
  have hwalk :=
    rhsArgsS_instantiate0_telWhnfDom hE (.const w.recRef w.ls) w.preMajor
      w.nparams w.nMinors w.fuel fr fs hNF hD
  rw [← hwalk] at htail
  exact htail

/-! ## (27) Mixed induction: `iotaArgs` images to `rhsArgsS`

The cons cases are `nonrecursive_stepWhnf` and `recursive0_stepWhnf`.
Each takes the tail as a hypothesis, so the induction is that
hypothesis at every suffix. `.recursive 0` reads `piTelescopeFuel`'s
body; `whnfFuel_of_piTelescope_nil` is that body at the same fuel, and
`domsConstHeadFor` on the schema telescope supplies the const head.
`.recursive (k+1)` is excluded by `NoFunShapes`. Not `instPrefix_step`.
Not `envCorrAnnDWC_of_envWfT`. No `exprClosedAt`. `closure_claim` stays 0. -/

private theorem fieldBvars_cons (n : Nat) :
    fieldBvars (n + 1) = .bvar n :: fieldBvars n := by
  unfold fieldBvars
  rw [List.range_succ, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.singleton_append]

private theorem whnfFuel_of_piTelescope_nil {E : ResolvedEnv} {fuel : Nat}
    {A body : Expr Nat} (h : piTelescopeFuel E fuel A = some ([], body)) :
    whnfFuel E fuel A = some body := by
  obtain ⟨f, rfl, hw⟩ := piTel_nil_whnf E h
  exact whnfFuel_mono E (Nat.le_succ f) hw

private theorem appsSpine_of_spineHeadConst {e : Expr Nat}
    (h : spineHeadConst e = true) :
    ∃ r ls, (appsSpine e).1 = .const r ls := by
  unfold spineHeadConst at h
  split at h
  · rename_i r ls hr
    exact ⟨r, ls, hr⟩
  · exact Bool.noConfusion h

/-- The image of a successful `iotaArgs` walk equals `rhsArgsS` on
    `telWhnfDom` of `instPrefix` after `instantiateLevels`. The field
    list is `fieldBvars n`, sent to `fs`. The schema telescope carries
    `domsConstHeadFor` and `ConstsArity`; the image telescope carries
    `domsConstHeadFor` for the continuation. -/
theorem iotaArgs_rhsArgsS_telWhnfDom {E : ResolvedEnv}
    (hE : EnvClosed E) (hEL : EnvLevelsT E) (hEA : EnvConstsArity E)
    (w : IotaWitnessS E) :
    ∀ (n : Nat) (fs : List (Expr Nat)) (ss : List FieldShape)
      (T : Expr Nat) (args : List (Expr Nat)),
      ss.length = n → fs.length = n → NoFunShapes ss →
      (fieldBvars n).map (fun a =>
        instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) = fs →
      domsConstHeadFor E w.fuel ss T → ConstsArity E T →
      domsConstHeadFor E w.fuel ss
        (instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls T)) →
      iotaArgs E w.fuel
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors ss (fieldBvars n) T = some args →
      args.map (fun a =>
          instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
        rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          fs ss
          (telWhnfDom E w.fuel
            (instPrefix (w.preMajor ++ w.fields)
              (instantiateLevels w.ls T))) := by
  intro n
  induction n with
  | zero =>
      intro fs ss T args hlenS hlenF _ _ _ _ _ hargs
      have hss : ss = [] := by
        cases ss with
        | nil => rfl
        | cons _ _ => rw [List.length_cons] at hlenS; omega
      have hfs : fs = [] := by
        cases fs with
        | nil => rfl
        | cons _ _ => rw [List.length_cons] at hlenF; omega
      subst hss; subst hfs
      have hnil : fieldBvars 0 = [] := by
        simp only [fieldBvars, List.range_zero, List.reverse_nil, List.map_nil]
      rw [hnil, iotaArgs.eq_1] at hargs
      injection hargs with hargs
      subst hargs
      rfl
  | succ m ih =>
      intro fs ss T args hlenS hlenF hNF himg hSch hC hD hargs
      cases ss with
      | nil => rw [List.length_nil] at hlenS; omega
      | cons s ss =>
        cases fs with
        | nil => rw [List.length_nil] at hlenF; omega
        | cons fr fs =>
          have hlenS' : ss.length = m := by
            rw [List.length_cons] at hlenS; omega
          have hlenF' : fs.length = m := by
            rw [List.length_cons] at hlenF; omega
          have hNF' : NoFunShapes ss :=
            fun s' hs' k => hNF s' (List.mem_cons_of_mem _ hs') k
          have hfb := fieldBvars_cons m
          rw [hfb] at himg hargs
          simp only [List.map_cons] at himg
          injection himg with hf himg'
          obtain ⟨A, B, rfl⟩ := pi_of_domsConstHeadFor hSch
          have hIm :
              instPrefix (w.preMajor ++ w.fields)
                  (instantiateLevels w.ls (.pi A B)) =
                .pi (instPrefix (w.preMajor ++ w.fields)
                    (instantiateLevels w.ls A))
                  (instTel (w.preMajor ++ w.fields)
                    (instantiateLevels w.ls B)) := by
            rw [show instantiateLevels w.ls (.pi A B) =
                .pi (instantiateLevels w.ls A) (instantiateLevels w.ls B) from rfl]
            exact instPrefix_pi (w.preMajor ++ w.fields) _ _
          rw [hIm] at hD
          have hPair : ConstsArity E A ∧ ConstsArity E B := by
            simpa only [ConstsArity] using hC
          cases s with
          | nonrecursive =>
              simp only [domsConstHeadFor] at hSch hD
              rw [iotaArgs.eq_2] at hargs
              obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some'.mp hargs
              have hSchT :=
                domsConstHeadFor_instantiate hE hSch 0 (.bvar m)
              have hCT :=
                ConstsArity_instantiate 0 (.bvar m) trivial B hPair.2
              have hbody :=
                recursive0_bodyImg (w.preMajor ++ w.fields) m w.ls B
              have hbv :
                  instPrefix (w.preMajor ++ w.fields) (.bvar m) = fr := by
                simpa only [instantiateLevels] using hf
              rw [hbv] at hbody
              unfold instantiate0 at hbody
              have hDT := domsConstHeadFor_instantiate hE hD 0 fr
              rw [← hbody] at hDT
              have htail := ih fs ss (instantiate0 (.bvar m) B) rest
                hlenS' hlenF' hNF' himg' hSchT hCT hDT hrest
              rw [← heq]
              exact nonrecursive_stepWhnf hE w m fr A B rest fs ss
                hf hNF' hD htail
          | recursive k =>
              cases k with
              | succ j =>
                  exact absurd rfl
                    (hNF (.recursive (j + 1)) (List.mem_cons_self _ _) j)
              | zero =>
                  simp only [domsConstHeadFor] at hSch hD
                  obtain ⟨⟨body0, hw0, hsc⟩, hSchB⟩ := hSch
                  rw [iotaArgs.eq_3] at hargs
                  cases hpt : piTelescopeFuel E w.fuel A with
                  | none =>
                      rw [hpt] at hargs
                      exact Option.noConfusion hargs
                  | some p =>
                      obtain ⟨doms, famApp⟩ := p
                      cases doms with
                      | cons _ _ =>
                          rw [hpt] at hargs
                          exact Option.noConfusion hargs
                      | nil =>
                          rw [hpt] at hargs
                          obtain ⟨rest, hrest, heq⟩ :=
                            Option.map_eq_some'.mp hargs
                          have hw := whnfFuel_of_piTelescope_nil hpt
                          have hbodyEq : body0 = famApp := by
                            rw [hw] at hw0
                            exact (Option.some.inj hw0).symm
                          rw [hbodyEq] at hsc
                          obtain ⟨r, us, hsp⟩ :=
                            appsSpine_of_spineHeadConst hsc
                          have hSchT :=
                            domsConstHeadFor_instantiate hE hSchB 0 (.bvar m)
                          have hCT :=
                            ConstsArity_instantiate 0 (.bvar m) trivial B hPair.2
                          obtain ⟨_, hDbody⟩ := hD
                          have hbody :=
                            recursive0_bodyImg (w.preMajor ++ w.fields) m w.ls B
                          have hbv :
                              instPrefix (w.preMajor ++ w.fields) (.bvar m) = fr := by
                            simpa only [instantiateLevels] using hf
                          rw [hbv] at hbody
                          unfold instantiate0 at hbody
                          have hDT := domsConstHeadFor_instantiate hE hDbody 0 fr
                          rw [← hbody] at hDT
                          have htail := ih fs ss (instantiate0 (.bvar m) B) rest
                            hlenS' hlenF' hNF' himg' hSchT hCT hDT hrest
                          rw [heq.symm]
                          exact recursive0_stepWhnf hE hEL hEA w m fr A famApp B
                            rest fs ss hPair.1 hw hsp hf hNF' hDbody htail

/-! ## (28) `domsConstHeadFor` survives `instPrefix` and `lift`

The witness application of `iotaArgs_rhsArgsS_telWhnfDom` needs the
predicate on `instPrefix` of the level image, and on `lift` of the
stored field telescope. One `instPrefix` step is
`domsConstHeadFor_instantiate`. The lift step is the already-proved
`whnfFuel_lift` plus `spineHeadConst_lift`. Not `instPrefix_step`.
Not `envCorrAnnDWC_of_envWfT`. No `exprClosedAt`. `closure_claim` stays 0. -/

theorem domsConstHeadFor_instPrefix {E : ResolvedEnv}
    (hE : EnvClosed E) {fuel : Nat} {shapes : List FieldShape} {T : Expr Nat}
    (h : domsConstHeadFor E fuel shapes T) (args : List (Expr Nat)) :
    domsConstHeadFor E fuel shapes (instPrefix args T) := by
  induction args generalizing T with
  | nil =>
      rw [instPrefix_nil]
      exact h
  | cons a as ih =>
      rw [instPrefix_cons]
      exact ih (domsConstHeadFor_instantiate hE h as.length (lift 0 as.length a))

theorem domsConstHeadFor_lift {E : ResolvedEnv}
    (hE : EnvClosed E) {fuel : Nat} {shapes : List FieldShape} {T : Expr Nat}
    (h : domsConstHeadFor E fuel shapes T) (c a : Nat) :
    domsConstHeadFor E fuel shapes (lift c a T) := by
  induction shapes generalizing T c with
  | nil => trivial
  | cons s ss ih =>
      obtain ⟨A, B, rfl⟩ := pi_of_domsConstHeadFor h
      cases s with
      | nonrecursive =>
          simp only [domsConstHeadFor, lift] at h ⊢
          exact ih h (c + 1)
      | recursive k =>
          cases k with
          | succ _ =>
              simp only [domsConstHeadFor] at h
          | zero =>
              simp only [domsConstHeadFor] at h
              obtain ⟨⟨w, hw, hsc⟩, htail⟩ := h
              have hlift := whnfFuel_lift E hE c a fuel A
              rw [hw, Option.map_some'] at hlift
              simp only [lift]
              exact ⟨⟨lift c a w, hlift, spineHeadConst_lift c a w hsc⟩,
                ih htail (c + 1)⟩

/-! ## (29) Witness application of the mixed induction

`hschema` walks `lift` of `ctorFieldTelRaw`. `domsConstHeadFor_lift`
and `ConstsArity_lift` put the schema premises there. The image
premise is `domsConstHeadFor` on `ctorFieldTelInst`, rewritten along
`ctorFieldTelInst_eq_schemaLift`. `iotaRhsOfS_eq_fold` is the schema
factor. `fieldsTelS` at that image is already
`fieldsTelS_ctorFieldTelInst_of_envWfT`. Not `instPrefix_step`.
No `exprClosedAt`. `closure_claim` stays 0. -/

theorem iotaRhsOfS_eq_rhsArgsS_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E) (hNF : NoFunShapes w.shapes)
    {minor : Expr Nat}
    (hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor) :
    iotaRhsOfS w =
      foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors w.fields w.shapes
        (telWhnfDom E w.fuel (ctorFieldTelInst w))) := by
  have hE := envClosed_of_envWfT hW
  have hEL := envWfT_levels hW
  have hEA := envConstsArity_of_envWfT hW
  have hpeelLen : w.ctorDoms.length = w.nparams + w.fields.length :=
    peelPis_length (w.nparams + w.fields.length) w.ctorMember.mtype w.hpeel
  have hdrop : (w.ctorDoms.drop w.nparams).length = w.fields.length := by
    rw [List.length_drop, hpeelLen]
    omega
  have hsh : w.shapes.length = w.fields.length := by
    rw [fieldShapesFuel_length E (w.ctorDoms.drop w.nparams) w.hshapes, hdrop]
  have hraw : domsConstHeadFor E w.fuel w.shapes
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) := by
    simpa only [ctorFieldTelRaw] using
      domsConstHeadFor_foldr w.nparams (w.ctorDoms.drop w.nparams)
        w.hshapes hNF (Nat.le_refl _)
  have hCraw := ctorFieldTelRaw_constsArity_of_envWfT hW w
  have hSch := domsConstHeadFor_lift hE hraw 0
    (w.fields.length + 1 + w.nMinors + w.nindices)
  have hC := ConstsArity_lift 0
    (w.fields.length + 1 + w.nMinors + w.nindices)
    (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult) hCraw
  have hDonInst : domsConstHeadFor E w.fuel w.shapes (ctorFieldTelInst w) := by
    unfold ctorFieldTelInst
    exact domsConstHeadFor_instPrefix hE
      (domsConstHeadFor_instantiateLevels hEL hEA hraw hCraw
        (w.ls.take w.ctorMember.arity))
      (w.preMajor.take w.nparams)
  have hD := hDonInst
  rw [← ctorFieldTelInst_eq_schemaLift hW w] at hD
  have himg : (fieldBvars w.fields.length).map
      (fun a => instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls a)) =
      w.fields := by
    conv =>
      rhs
      rw [← fieldBvars_instPrefix_fields w]
    apply List.map_congr_left
    intro a ha
    unfold fieldBvars at ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    rfl
  have hopen := w.hschema
  simp only [iotaOpenRhs, Option.map_eq_some'] at hopen
  obtain ⟨args, hargs, _⟩ := hopen
  have hwalk := iotaArgs_rhsArgsS_telWhnfDom hE hEL hEA w
    w.fields.length w.fields w.shapes
    (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))
    args hsh rfl hNF himg hSch hC hD hargs
  rw [iotaRhsOfS_eq_fold w hargs hm, hwalk, ctorFieldTelInst_eq_schemaLift hW w]

/-- `EnvWfT` gives `EnvCorrAnnDWC`. The gate is `NoFunShapes` inside the
    certificate. `.recursive (k+1)` stays excluded. `closure_claim` stays 0. -/
theorem envCorrAnnDWC_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    EnvCorrAnnDWC E := by
  refine envCorrAnnDWC_of_instPrefix_image ?_
  intro w hNF
  refine ⟨fieldsTelS_ctorFieldTelInst_of_envWfT hW w hNF, ?_⟩
  intro minor hm
  exact iotaRhsOfS_eq_rhsArgsS_of_envWfT hW w hNF hm

/-- Every frec-free witness passes the W-union, so the gated certificate
    is `EnvCorrAnnDW`. One frec witness still refutes the ungated
    certificate. `closure_claim` stays 0. -/
theorem envCorrAnnDW_of_envCorrAnnDWC {E : ResolvedEnv}
    (h : EnvCorrAnnDWC E)
    (hNF : ∀ w : IotaWitnessS E, NoFunShapes w.shapes) :
    EnvCorrAnnDW E :=
  fun w => h w (hNF w)

/-- `EnvWfT` and per-witness `NoFunShapes` give `CorrCertsBelowDW`,
    the premise `iotaPreserveTTDW` reads. The frec gate stays named.
    `closure_claim` stays 0. -/
theorem corrCertsBelowDW_of_envWfT_noFun {E : ResolvedEnv}
    (hW : EnvWfT E)
    (hNF : ∀ w : IotaWitnessS E, NoFunShapes w.shapes) :
    CorrCertsBelowDW E :=
  .inr (envCorrAnnDW_of_envCorrAnnDWC (envCorrAnnDWC_of_envWfT hW) hNF)

/-- `iotaPreserveTTDW` with `CorrCertsBelowDW` paid by `EnvWfT` and
    `NoFunShapes`. `InScope` and `NormCorrDW` stay premises.
    `closure_claim` stays 0. -/
theorem iotaPreserveTTDW_of_noFun {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hselD : ∀ EA : ResolvedEnvA, ∀ _C : AnnEnvA EA, eraseEnv EA = E →
      ∀ w : IotaWitnessS E,
        iotaWitnessSAnnDArmW E w = true → NormCorrDW EA w)
    (hNF : ∀ w : IotaWitnessS E, NoFunShapes w.shapes)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveTTDW hW hP hΓ hselD
    (corrCertsBelowDW_of_envWfT_noFun hW hNF) hd hlhs

/-- `iotaPreserveTDW` with the same payment. `closure_claim` stays 0. -/
theorem iotaPreserveTDW_of_noFun {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hselD : ∀ EA : ResolvedEnvA, ∀ _C : AnnEnvA EA, eraseEnv EA = E →
      ∀ w : IotaWitnessS E,
        iotaWitnessSAnnDArmW E w = true → NormCorrDW EA w)
    (hNF : ∀ w : IotaWitnessS E, NoFunShapes w.shapes)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveTDW hW hP hΓ hselD
    (corrCertsBelowDW_of_envWfT_noFun hW hNF) hd hlhs

/-- `EnvNormEraseA` makes `ctorShapesA` agree on `normA.getD mtypeA` and
    `mtypeA`. A missing `normA` is the stored type. `closure_claim` stays 0. -/
theorem ctorShapesA_getD_of_envNormErase {EA : ResolvedEnvA}
    (hn : EnvNormEraseA EA) {c : Nat} {cm : CheckedMemberA}
    (hc : EA.members c = some cm) (hk : cm.mclass = .constructorM)
    (f nparams : Nat) :
    ctorShapesA f nparams (cm.normA.getD cm.mtypeA) =
      ctorShapesA f nparams cm.mtypeA := by
  cases hN : cm.normA with
  | none => simp [hN]
  | some T =>
      simpa [hN] using
        ctorShapesA_of_erase (fam := f) (nparams := nparams)
          (hn c cm hc hk T hN)

/-- A `ctorShapesA` read that `EnvNoFunA` accepts is `NoFunShapes`.
    `.recursive (k+1)` is the excluded shape. `closure_claim` stays 0. -/
theorem noFunShapes_of_envNoFunA {EA : ResolvedEnvA}
    (hnf : EnvNoFunA EA) {c : Nat} {cm : CheckedMemberA} {f : Nat}
    {fm : CheckedMemberA} {shapes : List FieldShape}
    (hc : EA.members c = some cm) (hk : cm.mclass = .constructorM)
    (hf : memberFamRefA cm = some f) (hfm : EA.members f = some fm)
    (hs : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some shapes) :
    NoFunShapes shapes :=
  hnf c cm f fm shapes hc hk hf hfm hs

/-- On an erased witness whose field domains are a direct fragment,
    `EnvNoFunA` and `EnvNormEraseA` give `NoFunShapes` when the annotated
    constructor's family reference and parameter count are the witness's.
    Those two facts stay hypotheses. Not `EnvWfT` alone.
    `closure_claim` stays 0. -/
theorem noFunShapes_of_envNoFunA_witness {EA : ResolvedEnvA}
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (w : IotaWitnessS (eraseEnv EA))
    (hF : ∀ j (hj : j < (w.ctorDoms.drop w.nparams).length), ∃ F,
      DirectFieldFrag (eraseEnv EA) F w.familyRef w.famMember.arity w.nparams
        w.nindices (w.nparams + j) ((w.ctorDoms.drop w.nparams)[j]))
    {ctorA : CheckedMemberA} (hcE : eraseMember ctorA = w.ctorMember)
    (hc : EA.members w.ctorRef = some ctorA)
    (hf : memberFamRefA ctorA = some w.familyRef)
    {fm : CheckedMemberA} (hfm : EA.members w.familyRef = some fm)
    (hnpar : fm.nparamsA = w.nparams) :
    NoFunShapes w.shapes := by
  have hk : ctorA.mclass = .constructorM := by
    have hm : ctorA.mclass = w.ctorMember.mclass := by
      unfold eraseMember at hcE
      exact congrArg CheckedMember.mclass hcE
    exact hm.trans w.hctorK
  have hshapes := ctorShapesA_of_witnessS w hF hcE
  have hs : ctorShapesA w.familyRef fm.nparamsA
      (ctorA.normA.getD ctorA.mtypeA) = some w.shapes := by
    rw [hnpar, ctorShapesA_getD_of_envNormErase hn hc hk w.familyRef w.nparams]
    exact hshapes
  exact noFunShapes_of_envNoFunA hnf hc hk hf hfm hs

/-- `piResult` on an erasure is the erasure of `piBodyA`. The binder
    sorts are forgotten. `closure_claim` stays 0. -/
theorem piResult_erase : (T : ExprA) → piResult (erase T) = erase (piBodyA T)
  | .pi _ _ B _ => by
      simp only [erase, piResult, piBodyA]
      exact piResult_erase B
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- A spine head reference survives erasure. A non-`const` head is
    `none` on both sides. `closure_claim` stays 0. -/
theorem spineHeadRef_erase (e : ExprA) :
    spineHeadRef (erase e) = spineHeadRefA e := by
  unfold spineHeadRef spineHeadRefA
  rw [appsSpineA_erase]
  cases (appsSpineA e).1 with
  | const _ _ => rfl
  | bvar _ => rfl
  | sort _ => rfl
  | app _ _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

/-- On a constructor, `memberFamRefA` is `memberFamRef` of the erasure.
    The read is the result spine. Not `EnvWfT`. `closure_claim` stays 0. -/
theorem memberFamRefA_eq_memberFamRef_erase {m : CheckedMemberA}
    (hk : m.mclass = .constructorM) :
    memberFamRefA m = memberFamRef (eraseMember m) := by
  unfold memberFamRefA memberFamRef eraseMember
  rw [hk]
  simp only
  rw [piResult_erase, spineHeadRef_erase]

/-- An erased witness's constructor declares `w.familyRef`.
    `memberFamRef_ctorMemberS` is the erased read. Not `EnvWfT`.
    Not `fm.nparamsA = w.nparams`. `closure_claim` stays 0. -/
theorem memberFamRefA_of_witnessS {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA))
    {ctorA : CheckedMemberA} (hcE : eraseMember ctorA = w.ctorMember) :
    memberFamRefA ctorA = some w.familyRef := by
  have hk : ctorA.mclass = .constructorM := by
    have hm : ctorA.mclass = w.ctorMember.mclass :=
      congrArg CheckedMember.mclass hcE
    exact hm.trans w.hctorK
  rw [memberFamRefA_eq_memberFamRef_erase hk, hcE]
  exact memberFamRef_ctorMemberS w

/-- The direct-fragment witness is `NoFunShapes` once the parameter
    count is the witness's. The family reference is
    `memberFamRefA_of_witnessS`. Not `EnvWfT` alone.
    `closure_claim` stays 0. -/
theorem noFunShapes_of_envNoFunA_witness_fam {EA : ResolvedEnvA}
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (w : IotaWitnessS (eraseEnv EA))
    (hF : ∀ j (hj : j < (w.ctorDoms.drop w.nparams).length), ∃ F,
      DirectFieldFrag (eraseEnv EA) F w.familyRef w.famMember.arity w.nparams
        w.nindices (w.nparams + j) ((w.ctorDoms.drop w.nparams)[j]))
    {ctorA : CheckedMemberA} (hcE : eraseMember ctorA = w.ctorMember)
    (hc : EA.members w.ctorRef = some ctorA)
    {fm : CheckedMemberA} (hfm : EA.members w.familyRef = some fm)
    (hnpar : fm.nparamsA = w.nparams) :
    NoFunShapes w.shapes :=
  noFunShapes_of_envNoFunA_witness hnf hn w hF hcE hc
    (memberFamRefA_of_witnessS w hcE) hfm hnpar

/-- `nparamsA` is not read by `eraseMember`. Two annotations of one
    member erase to one tree member. Not a derivation of
    `fm.nparamsA = w.nparams`. `closure_claim` stays 0. -/
theorem eraseMember_nparamsA (m : CheckedMemberA) (k : Nat) :
    eraseMember { m with nparamsA := k } = eraseMember m := rfl

/-- Under `EnvWfA`, the family at an erased witness's `familyRef` has
    `nparamsA = w.nparams`. The split is the view's parameter list
    against the witness's index count. Not `EnvWfT`.
    `eraseMember_nparamsA` is why the erasure equation is not enough.
    `closure_claim` stays 0. -/
theorem nparamsA_of_witnessS {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (w : IotaWitnessS (eraseEnv EA))
    {fm : CheckedMemberA} (hfm : EA.members w.familyRef = some fm) :
    fm.nparamsA = w.nparams := by
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  have hrK : recA.mclass = .recursorM :=
    (congrArg CheckedMember.mclass hrE).trans w.hrecK
  obtain ⟨E₀, f, fmG, fv, cs, rec, href, hmem, _, hfresh, _, hpre, _⟩ :=
    envWfA_recGroup hW w.recRef recA hrA hrK
  have hst : recA.mtypeA = groupRecTypeA fv cs rec.elim := by
    rw [← hmem]; exact rec.stored
  have hrT : erase recA.mtypeA = w.recMember.mtype :=
    congrArg CheckedMember.mtype hrE
  have hcnt : piCountA recA.mtypeA =
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  have hpeel := piDomsA_erase_peelPis recA.mtypeA
  rw [hcnt, hrT, w.hpeelRec] at hpeel
  injection hpeel with hpeel
  injection hpeel with hdoms hbody
  have hlenD : (piDomsA recA.mtypeA).length =
      w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    have hlen := congrArg List.length hdoms
    rw [List.length_map, peelPis_length _ _ w.hpeelRec] at hlen
    exact hlen.symm
  obtain ⟨D, hD, hDe⟩ := getElem?_map_erase hdoms.symm w.hmajorTy
  have hlast : (piDomsA recA.mtypeA).getLast? = some D := by
    rw [List.getLast?_eq_getElem?, hlenD]
    exact hD
  have hlastB : (piDomsA recA.mtypeA).getLast? =
      some (liftA fv.indices.length
        ((cs.reverse.map GroupCtorA.minorData).length + 1)
        (famLocalsA f (canonLevelsA fmG.arity) fv.params.length
          fv.indices.length)) := by
    rw [hst, groupRecTypeA]
    exact piDomsA_recTypeA_getLast f (canonLevelsA fmG.arity) fv.params
      fv.indices fv.sort (rec.elim.motiveLevel fmG.arity)
      (cs.reverse.map GroupCtorA.minorData)
  have hDB : D = liftA fv.indices.length
      ((cs.reverse.map GroupCtorA.minorData).length + 1)
      (famLocalsA f (canonLevelsA fmG.arity) fv.params.length
        fv.indices.length) :=
    Option.some.inj (by rw [hlast] at hlastB; exact hlastB)
  have hhead := appsSpineA_majorDom f (canonLevelsA fmG.arity)
    fv.params.length fv.indices.length
    ((cs.reverse.map GroupCtorA.minorData).length + 1)
  rw [← hDB] at hhead
  have hDsp : appsSpine (erase D) =
      (.const w.familyRef ((List.range w.famMember.arity).map Level.param),
        (List.range w.nparams).reverse.map
          (fun i => Expr.bvar (i + w.nindices + w.nMinors + 1)) ++
          (List.range w.nindices).reverse.map (fun i => Expr.bvar i)) := by
    rw [hDe, appsSpine_foldApps]
    rfl
  obtain ⟨_, hDA, _⟩ := appsSpineA_of_erase_const hDsp
  have hf : f = w.familyRef := by
    have h1 := congrArg Prod.fst hDA
    rw [hhead] at h1
    injection h1 with hf _
  have hmemF : (groupEnvA E₀ f fmG (cs.map GroupCtorA.entry)).members f =
      some fmG := members_groupEnvA_family hfresh
  have hmemR : (groupRecEnvA cs rec).members f = some fmG := by
    unfold groupRecEnvA
    have hne : f ≠ f + 1 + cs.length := fun h => by omega
    rw [members_extendEnvA_ne _ _ _ hne]
    exact hmemF
  have hEA : EA.members w.familyRef = some fmG := by
    rw [← hf]
    exact hpre f fmG hmemR
  have hfmEq : fm = fmG := Option.some.inj (hfm.symm.trans hEA)
  subst hfmEq
  have hblen : (appsSpineA (piBodyA recA.mtypeA)).2.length =
      fv.indices.length + 1 := by
    rw [hst, groupRecTypeA, piBodyA_recTypeA]
    exact appsSpineA_recBodyA _ _
  have hBlen : (appsSpine (erase (piBodyA recA.mtypeA))).2.length =
      w.nindices + 1 := by
    rw [← hbody, w.hrecBody, appsSpine_foldApps]
    rw [show appsSpine (.bvar (w.nMinors + w.nindices + 1)) =
        (.bvar (w.nMinors + w.nindices + 1), []) from rfl]
    simp only [List.nil_append, List.length_append, List.length_map,
      List.length_reverse, List.length_range, List.length_singleton]
  have hsame : (appsSpine (erase (piBodyA recA.mtypeA))).2.length =
      (appsSpineA (piBodyA recA.mtypeA)).2.length := by
    rw [appsSpineA_erase]
    simp only [List.length_map]
  have hni : fv.indices.length = w.nindices := by
    have h1 : fv.indices.length + 1 = w.nindices + 1 :=
      hblen.symm.trans (hsame.symm.trans hBlen)
    omega
  have herase : eraseMember fm = w.famMember := by
    have hmap := members_eraseEnv EA w.familyRef
    rw [hEA, w.hfam] at hmap
    exact Option.some.inj hmap.symm
  have hpc : piCountA fm.mtypeA = w.nparams + w.nindices := by
    have hty : erase fm.mtypeA = w.famMember.mtype := by
      rw [show erase fm.mtypeA = (eraseMember fm).mtype from rfl, herase]
    rw [← piCountA_erase, hty, w.hnidx]
  rw [piCountA_famView fv, fv.nparams, hni] at hpc
  exact Nat.add_right_cancel hpc

/-- `EnvWfA` pays both hypotheses of `noFunShapes_of_envNoFunA_witness`.
    The family reference is the erasure. The parameter count is the
    view. Not `EnvWfT` alone. `closure_claim` stays 0. -/
theorem noFunShapes_of_envWfA_witness {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (w : IotaWitnessS (eraseEnv EA))
    (hF : ∀ j (hj : j < (w.ctorDoms.drop w.nparams).length), ∃ F,
      DirectFieldFrag (eraseEnv EA) F w.familyRef w.famMember.arity w.nparams
        w.nindices (w.nparams + j) ((w.ctorDoms.drop w.nparams)[j]))
    {ctorA : CheckedMemberA} (hcE : eraseMember ctorA = w.ctorMember)
    (hc : EA.members w.ctorRef = some ctorA)
    {fm : CheckedMemberA} (hfm : EA.members w.familyRef = some fm) :
    NoFunShapes w.shapes :=
  noFunShapes_of_envNoFunA_witness_fam hnf hn w hF hcE hc hfm
    (nparamsA_of_witnessS hW w hfm)

/-- `EnvCorrAnnCert` supplies the direct fragment. `EnvWfA` supplies
    the family reference and the parameter count. Not `EnvWfT` alone.
    `closure_claim` stays 0. -/
theorem noFunShapes_of_envWfA_cert {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hC : EnvCorrAnnCert (eraseEnv EA))
    (w : IotaWitnessS (eraseEnv EA)) : NoFunShapes w.shapes := by
  obtain ⟨ctorA, hc, hcE⟩ := members_of_eraseEnv w.hctor
  obtain ⟨fm, hfm, _⟩ := members_of_eraseEnv w.hfam
  exact noFunShapes_of_envWfA_witness hW hnf hn w
    (fun j hj => ⟨domsFuelBound (w.ctorDoms.drop w.nparams),
      (iotaWitnessSAnnB_parts (hC w)).1 j hj⟩) hcE hc hfm

/-- `EnvWfT` gives the gated certificate. `EnvWfA`, `EnvNoFunA`,
    `EnvNormEraseA`, and `EnvCorrAnnCert` pay `NoFunShapes` on the
    erasure. Not `EnvWfT` alone. `InScope` and `NormCorrDW` stay.
    `closure_claim` stays 0. -/
theorem envCorrAnnDW_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfT (eraseEnv EA)) (hWA : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hC : EnvCorrAnnCert (eraseEnv EA)) :
    EnvCorrAnnDW (eraseEnv EA) :=
  envCorrAnnDW_of_envCorrAnnDWC (envCorrAnnDWC_of_envWfT hW)
    (fun w => noFunShapes_of_envWfA_cert hWA hnf hn hC w)

/-- The same payment is `CorrCertsBelowDW`. `InScope` and `NormCorrDW`
    stay on the preservation theorems. Not `EnvWfT` alone.
    `closure_claim` stays 0. -/
theorem corrCertsBelowDW_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfT (eraseEnv EA)) (hWA : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hC : EnvCorrAnnCert (eraseEnv EA)) :
    CorrCertsBelowDW (eraseEnv EA) :=
  .inr (envCorrAnnDW_of_envWfA hW hWA hnf hn hC)

/-- `iotaPreserveTTDW` with `NoFunShapes` paid by the annotated premises.
    `InScope` and `NormCorrDW` stay. Not `EnvWfT` alone.
    `closure_claim` stays 0. -/
theorem iotaPreserveTTDW_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfT (eraseEnv EA)) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT (eraseEnv EA) n Γ)
    (hselD : ∀ EB : ResolvedEnvA, ∀ _C : AnnEnvA EB,
      eraseEnv EB = eraseEnv EA →
      ∀ w : IotaWitnessS (eraseEnv EA),
        iotaWitnessSAnnDArmW (eraseEnv EA) w = true → NormCorrDW EB w)
    (hWA : EnvWfA I EA) (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hC : EnvCorrAnnCert (eraseEnv EA))
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT (eraseEnv EA) lhs rhs)
    (hlhs : HasTyT (eraseEnv EA) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv EA) n Γ rhs T) :=
  iotaPreserveTTDW hW hP hΓ hselD
    (corrCertsBelowDW_of_envWfA hW hWA hnf hn hC) hd hlhs

/-- `iotaPreserveTDW` with the same payment. `closure_claim` stays 0. -/
theorem iotaPreserveTDW_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfT (eraseEnv EA)) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT (eraseEnv EA) n Γ)
    (hselD : ∀ EB : ResolvedEnvA, ∀ _C : AnnEnvA EB,
      eraseEnv EB = eraseEnv EA →
      ∀ w : IotaWitnessS (eraseEnv EA),
        iotaWitnessSAnnDArmW (eraseEnv EA) w = true → NormCorrDW EB w)
    (hWA : EnvWfA I EA) (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hC : EnvCorrAnnCert (eraseEnv EA))
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU (eraseEnv EA) lhs rhs)
    (hlhs : HasTyT (eraseEnv EA) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv EA) n Γ rhs T) :=
  iotaPreserveTDW hW hP hΓ hselD
    (corrCertsBelowDW_of_envWfA hW hWA hnf hn hC) hd hlhs

/-- `EnvNormEraseA` and `EnvCorrAnnCert` pay the count and the shape
    read of `NormCorrDW`. The `telWhnfDom` conjunct stays. Not
    `NormCorrDW`. Not `EnvWfT`. `closure_claim` stays 0. -/
theorem normCountShapes_of_envNormErase_cert {EA : ResolvedEnvA}
    (hn : EnvNormEraseA EA) (hC : EnvCorrAnnCert (eraseEnv EA))
    (w : IotaWitnessS (eraseEnv EA))
    {ctorA : CheckedMemberA} (hc : EA.members w.ctorRef = some ctorA) :
    piCountA (ctorA.normA.getD ctorA.mtypeA) =
        w.nparams + w.fields.length ∧
      ctorShapesA w.familyRef w.nparams
        (ctorA.normA.getD ctorA.mtypeA) = some w.shapes := by
  have hcE : eraseMember ctorA = w.ctorMember := by
    have hmap := members_eraseEnv EA w.ctorRef
    rw [hc, w.hctor] at hmap
    exact Option.some.inj hmap.symm
  have hk : ctorA.mclass = .constructorM := by
    have hm : ctorA.mclass = w.ctorMember.mclass :=
      congrArg CheckedMember.mclass hcE
    exact hm.trans w.hctorK
  have hgetD : erase (ctorA.normA.getD ctorA.mtypeA) =
      erase ctorA.mtypeA := by
    cases hNm : ctorA.normA with
    | none => rfl
    | some T => exact hn w.ctorRef ctorA hc hk T hNm
  have hcT : erase ctorA.mtypeA = w.ctorMember.mtype :=
    congrArg CheckedMember.mtype hcE
  have hcnt : piCountA ctorA.mtypeA = w.nparams + w.fields.length := by
    rw [← piCountA_erase, hcT, ← w.hnpar]
  have hpc : piCountA (ctorA.normA.getD ctorA.mtypeA) =
      piCountA ctorA.mtypeA := by
    rw [← piCountA_erase (ctorA.normA.getD ctorA.mtypeA),
      ← piCountA_erase ctorA.mtypeA, hgetD]
  have hshapes := ctorShapesA_of_witnessS w
    (fun j hj => ⟨domsFuelBound (w.ctorDoms.drop w.nparams),
      (iotaWitnessSAnnB_parts (hC w)).1 j hj⟩) hcE
  refine ⟨hpc.trans hcnt, ?_⟩
  rw [ctorShapesA_getD_of_envNormErase hn hc hk w.familyRef w.nparams]
  exact hshapes

/-- Under `EnvNormEraseA`, `applyTelA` on the normed constructor type
    erases to `applyTel` on the stored type. Not `telWhnfDom`.
    Not `NormCorrDW`. Not `EnvWfT`. `closure_claim` stays 0. -/
theorem erase_applyTelA_norm_of_envNormErase {EA : ResolvedEnvA}
    (hn : EnvNormEraseA EA) (w : IotaWitnessS (eraseEnv EA))
    {ctorA : CheckedMemberA} (hc : EA.members w.ctorRef = some ctorA)
    (args : List ExprA)
    (hargs : args.map erase = w.preMajor.take w.nparams) :
    (applyTelA args
        (instantiateLevelsA (w.ls.take w.ctorMember.arity)
          (ctorA.normA.getD ctorA.mtypeA))).map erase =
      applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          w.ctorMember.mtype) := by
  have hcE : eraseMember ctorA = w.ctorMember := by
    have hmap := members_eraseEnv EA w.ctorRef
    rw [hc, w.hctor] at hmap
    exact Option.some.inj hmap.symm
  have hk : ctorA.mclass = .constructorM :=
    (congrArg CheckedMember.mclass hcE).trans w.hctorK
  have hgetD : erase (ctorA.normA.getD ctorA.mtypeA) =
      erase ctorA.mtypeA := by
    cases hNm : ctorA.normA with
    | none => rfl
    | some T => exact hn w.ctorRef ctorA hc hk T hNm
  have hcT : erase ctorA.mtypeA = w.ctorMember.mtype :=
    congrArg CheckedMember.mtype hcE
  have happ := applyTelA_erase args
    (instantiateLevelsA (w.ls.take w.ctorMember.arity)
      (ctorA.normA.getD ctorA.mtypeA))
  rw [erase_instantiateLevelsA, hgetD, hcT, hargs] at happ
  exact happ

/-- The `telWhnfDom` read follows once the stored `applyTel` result
    is already that whnf. The identity stays a hypothesis. Not
    `NormCorrDW`. Not `EnvWfT`. Not a premise on `instPrefix`.
    `closure_claim` stays 0. -/
theorem normTelWhnf_of_stored_id {EA : ResolvedEnvA}
    (hn : EnvNormEraseA EA) (w : IotaWitnessS (eraseEnv EA))
    {ctorA : CheckedMemberA} (hc : EA.members w.ctorRef = some ctorA)
    (args : List ExprA)
    (hargs : args.map erase = w.preMajor.take w.nparams)
    {ctorAfterE : Expr Nat}
    (hE : applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          w.ctorMember.mtype) = some ctorAfterE)
    (hid : ctorAfterE =
      telWhnfDom (eraseEnv EA) w.fuel ctorAfterE) :
    ∃ ctorAfterA,
      applyTelA args
          (instantiateLevelsA (w.ls.take w.ctorMember.arity)
            (ctorA.normA.getD ctorA.mtypeA)) = some ctorAfterA ∧
        erase ctorAfterA =
          telWhnfDom (eraseEnv EA) w.fuel ctorAfterE := by
  have happ := erase_applyTelA_norm_of_envNormErase hn w hc args hargs
  rw [hE] at happ
  cases hA : applyTelA args
      (instantiateLevelsA (w.ls.take w.ctorMember.arity)
        (ctorA.normA.getD ctorA.mtypeA)) with
  | none =>
      rw [hA] at happ
      exact Option.noConfusion happ
  | some ctorAfterA =>
      rw [hA] at happ
      exact ⟨ctorAfterA, rfl, (Option.some.inj happ).trans hid⟩

/-- `EnvNormEraseA`, `EnvCorrAnnCert`, and the stored-telescope
    identity pay `NormCorrDW`. The identity stays a hypothesis.
    Not `EnvWfT`. `InScope` stays off this name.
    `closure_claim` stays 0. -/
theorem normCorrDW_of_stored_id {EA : ResolvedEnvA}
    (hn : EnvNormEraseA EA) (hC : EnvCorrAnnCert (eraseEnv EA))
    (w : IotaWitnessS (eraseEnv EA))
    (hid : ∀ {ctorAfterE : Expr Nat},
      applyTel (w.preMajor.take w.nparams)
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            w.ctorMember.mtype) = some ctorAfterE →
      ctorAfterE = telWhnfDom (eraseEnv EA) w.fuel ctorAfterE) :
    NormCorrDW EA w := by
  intro cm hc _
  have hcs := normCountShapes_of_envNormErase_cert hn hC w hc
  refine ⟨hcs.1, hcs.2, ?_⟩
  intro args hargs
  have hlen : (w.preMajor.take w.nparams).length = w.nparams := by
    rw [List.length_take]
    have hleN : w.nparams ≤ w.preMajor.length := by
      rw [w.hpre, Nat.add_assoc, Nat.add_assoc]
      exact Nat.le_add_right _ _
    exact Nat.min_eq_left hleN
  have hle : (w.preMajor.take w.nparams).length ≤
      piCount (instantiateLevels (w.ls.take w.ctorMember.arity)
        w.ctorMember.mtype) := by
    rw [hlen, piCount_instantiateLevels, ← w.hnpar]
    exact Nat.le_add_right _ _
  obtain ⟨ctorAfterE, hE⟩ := applyTel_some_of_piCount_le hle
  obtain ⟨ctorAfterA, hA, hwh⟩ :=
    normTelWhnf_of_stored_id hn w hc args hargs hE (hid hE)
  refine ⟨ctorAfterA, hA, ?_⟩
  intro ctorAfterE' hE'
  rw [Option.some.inj (hE'.symm.trans hE)]
  exact hwh

/-- At a concrete `AnnEnvA`, `NormCorrDW` inside `hasTyT_iota_srTDW` is
    `normCorrDW_of_stored_id`. The stored-telescope identity stays a
    hypothesis. `EnvWfT` of the erasure stays. Not `EnvWfT` alone.
    `InScope` stays off this name. `closure_claim` stays 0. -/
theorem hasTyT_iota_srTDW_of_stored_id {EA : ResolvedEnvA}
    (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hW : EnvWfT (eraseEnv EA))
    (hCert : EnvCorrAnnCert (eraseEnv EA))
    (hid : ∀ (w : IotaWitnessS (eraseEnv EA)) {ctorAfterE : Expr Nat},
      applyTel (w.preMajor.take w.nparams)
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            w.ctorMember.mtype) = some ctorAfterE →
      ctorAfterE = telWhnfDom (eraseEnv EA) w.fuel ctorAfterE)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT (eraseEnv EA) n Γ)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT (eraseEnv EA) lhs rhs)
    (hlhs : HasTyT (eraseEnv EA) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv EA) n Γ rhs T) := by
  refine hasTyT_iota_srTDW C hn ?_ ?_ hΓ hd hlhs
  · intro w _
    exact normCorrDW_of_stored_id hn hCert w (hid w)
  · obtain ⟨hWA⟩ := C.wf
    exact corrCertsBelowDW_of_envWfA hW hWA C.noFun hn hCert

/-- The `DerivedIotaU` cover at the same annotation. The legacy arm is
    `hasTyT_iota_sr`. The witness arm is the payment above. The identity
    stays a hypothesis. `InScope` stays off this name.
    `closure_claim` stays 0. -/
theorem hasTyT_iota_srUDW_of_stored_id {EA : ResolvedEnvA}
    (C : AnnEnvA EA) (hn : EnvNormEraseA EA)
    (hW : EnvWfT (eraseEnv EA))
    (hCert : EnvCorrAnnCert (eraseEnv EA))
    (hid : ∀ (w : IotaWitnessS (eraseEnv EA)) {ctorAfterE : Expr Nat},
      applyTel (w.preMajor.take w.nparams)
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            w.ctorMember.mtype) = some ctorAfterE →
      ctorAfterE = telWhnfDom (eraseEnv EA) w.fuel ctorAfterE)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT (eraseEnv EA) n Γ)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU (eraseEnv EA) lhs rhs)
    (hlhs : HasTyT (eraseEnv EA) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv EA) n Γ rhs T) := by
  obtain ⟨hWA⟩ := C.wf
  have hBelow := corrCertsBelowDW_of_envWfA hW hWA C.noFun hn hCert
  match hd with
  | .ofU w => exact hasTyT_iota_sr C hn hΓ (.of w) hlhs
  | .ofUS w =>
      exact hasTyT_iota_srTDW C hn
        (fun w _ => normCorrDW_of_stored_id hn hCert w (hid w))
        hBelow hΓ (.of w) hlhs

/-- `iotaPreserveTTDW` with `NormCorrDW` paid by the semantic prefix.
    `InScope` stays. `EnvCorrAnnCert` pays the count and the shapes.
    The stored-telescope identity stays a hypothesis. Not `EnvWfT`
    alone. Not a drop of the selector on `iotaPreserveTTDW_of_noFun`.
    `closure_claim` stays 0. -/
theorem iotaPreserveTTDW_of_stored_id {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hCert : EnvCorrAnnCert E)
    (hid : ∀ (w : IotaWitnessS E) {ctorAfterE : Expr Nat},
      applyTel (w.preMajor.take w.nparams)
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            w.ctorMember.mtype) = some ctorAfterE →
      ctorAfterE = telWhnfDom E w.fuel ctorAfterE)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_iota_srTDW C hn
    (fun w _ => normCorrDW_of_stored_id hn hCert w (hid w))
    (.inr (envCorrAnnDW_of_annCert hCert)) hΓ hd hlhs

/-- `iotaPreserveTDW` with the same payment. `InScope` stays.
    `closure_claim` stays 0. -/
theorem iotaPreserveTDW_of_stored_id {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hCert : EnvCorrAnnCert E)
    (hid : ∀ (w : IotaWitnessS E) {ctorAfterE : Expr Nat},
      applyTel (w.preMajor.take w.nparams)
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            w.ctorMember.mtype) = some ctorAfterE →
      ctorAfterE = telWhnfDom E w.fuel ctorAfterE)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  have hBelow : CorrCertsBelowDW (eraseEnv EA) :=
    .inr (envCorrAnnDW_of_annCert hCert)
  match hd with
  | .ofU w => exact hasTyT_iota_sr C hn hΓ (.of w) hlhs
  | .ofUS w =>
      exact hasTyT_iota_srTDW C hn
        (fun w _ => normCorrDW_of_stored_id hn hCert w (hid w))
        hBelow hΓ (.of w) hlhs

end Rcic.Declarative.Ann
