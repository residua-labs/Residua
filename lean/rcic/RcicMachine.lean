/-
RCIC reference machine — Batch A (Annex 21, M-1 carriers).

M-1: P-1 Ambient, P-2 AcceptedPayload/RunResult, P-3 RawTask extension.
Re-proves the 17 surviving RM* by field update. Residue strings corrected
per MR-6. MachineRed + whnfCert + convCert + inferCert + checkCert (M-2..M-6)
follow; kernelStepRaw (M-8) wires them; soundness rows are in RcicMachineSound.lean.

F-03 Batch A per docs/rcic/00_ANNEX_21_F03_DISPATCH.md at a2c4f33a9.
closure_claim stays 0.
-/
import rcic.RcicDeclarative
import rcic.RcicDTMeta
import rcic.RcicLevelDec
import rcic.RcicParRedIota
import rcic.RcicImportLevel

namespace Rcic.Machine
open Rcic.Declarative

/-! ## P-1: Ambient — 03 §4's raw kernel state binds ambient -/

structure Ambient where
  env : ResolvedEnv
  univs : Nat
  ctx : LCtx

/-! ## P-2: AcceptedPayload — 03 §6's five accepted payloads -/

inductive AcceptedPayload : Type
  | inferredType (T : Expr Nat) : AcceptedPayload
  | checked : AcceptedPayload
  | inferredWhnf (type whnf : Expr Nat) : AcceptedPayload
  | conversionConfirmed : AcceptedPayload
  | conversionMismatch : AcceptedPayload

inductive RunResult : Type
  | accepted (payload : AcceptedPayload) : RunResult
  | refused (residue : String) : RunResult
  | integrity (residue : String) : RunResult
  | suspended : RunResult

/-! ## P-3: RawTask — 03 §3's task forms (Batch A adds convAt + lookupDeclaration) -/

inductive RawTask : Type
  | infer (e : Expr Nat)
  | check (e A : Expr Nat)
  | whnfAt (A e : Expr Nat)
  | convType (A B : Expr Nat)
  | convAt (A l r : Expr Nat)
  | syntaxEqual (a b : Expr Nat)
  | levelEqual (l1 l2 : Level)
  | lookupLocal (i : Nat)
  | lookupDeclaration (r : Nat) (ls : List Level)
  deriving DecidableEq

/-! ## State (P-1) and step outcome -/

structure RawState where
  ambient : Ambient
  task : RawTask
  budget : Nat

inductive StepOutcome : Type
  | step (s' : RawState) : StepOutcome
  | result (r : RunResult) : StepOutcome

/-! ## RULING R: the residue channel — Cert α -/

inductive Cert (α : Type) : Type
  | ok (a : α) : Cert α
  | no (residue : String) : Cert α

/-! ## M-2: MachineRed — the machine's spine chain (maps OUT to Conv and ParRedStar) -/

inductive MachineRed (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (e : Expr Nat) : MachineRed E n Γ e e
  | headBeta (Γ : LCtx) (A body arg : Expr Nat)
      (rest : List (Expr Nat)) {c : Expr Nat}
      (k : MachineRed E n Γ (foldApps (instantiate0 arg body) rest) c) :
      MachineRed E n Γ (foldApps (.app (.lam A body) arg) rest) c
  | headZeta (Γ : LCtx) (A value body : Expr Nat)
      (rest : List (Expr Nat)) {c : Expr Nat}
      (k : MachineRed E n Γ (foldApps (instantiate0 value body) rest) c) :
      MachineRed E n Γ (foldApps (.letE A value body) rest) c
  | headDelta (Γ : LCtx) (r : Nat) (ls : List Level)
      (m : CheckedMember) (b : Expr Nat)
      (rest : List (Expr Nat))
      (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true) {c : Expr Nat}
      (k : MachineRed E n Γ (foldApps (instantiateLevels ls b) rest) c) :
      MachineRed E n Γ (foldApps (.const r ls) rest) c

/-- Spine bridge (M-2). -/
theorem machineSpineEq {e h : Expr Nat} {xs : List (Expr Nat)}
    (hs : appsSpine e = (h, xs)) : foldApps h xs = e := by
  have hfa := foldApps_appsSpine e
  rw [hs] at hfa
  exact hfa

/-- Conv spine congruence (M-2, machine-local copy under D-04 precedent). -/
def machineConvFoldApps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' : Expr Nat} (hf : Conv E n Γ f f') :
    (xs : List (Expr Nat)) → Conv E n Γ (foldApps f xs) (foldApps f' xs)
  | [] => hf
  | x :: xs =>
      machineConvFoldApps (.app Γ f f' x x hf (.refl Γ x)) xs

/-- Level-equality premises for branches 5/6 (M-2, E-P1-2 machine-local copies). -/
theorem machineEqN_refl (l : Level) : eqN l l := fun _ => rfl

theorem machineEqNList_refl : (ls : List Level) → eqNList ls ls
  | [] => True.intro
  | l :: ls => ⟨machineEqN_refl l, machineEqNList_refl ls⟩

theorem machineEqNList_of_eq {ls ls' : List Level}
    (h : ls = ls') : eqNList ls ls' :=
  h ▸ machineEqNList_refl ls

/-- First map: MachineRed → Conv (M-2, no EnvWf — no bvarZeta arm). -/
def machineRed_toConv {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → MachineRed E n Γ a b → Conv E n Γ a b
  | _, _, _, .refl Γ e => .refl Γ e
  | _, _, _, .headBeta Γ A body arg rest k =>
      .trans Γ _ _ _
        (machineConvFoldApps
          (.step Γ (.app (.lam A body) arg)
            (instantiate0 arg body) (.beta Γ A body arg)) rest)
        (machineRed_toConv k)
  | _, _, _, .headZeta Γ A value body rest k =>
      .trans Γ _ _ _
        (machineConvFoldApps
          (.step Γ (.letE A value body)
            (instantiate0 value body) (.zeta Γ A value body)) rest)
        (machineRed_toConv k)
  | _, _, _, .headDelta Γ r ls m b rest hres hbody htr k =>
      .trans Γ _ _ _
        (machineConvFoldApps
          (.step Γ (.const r ls) (instantiateLevels ls b)
            (.delta Γ r ls m b hres hbody htr)) rest)
        (machineRed_toConv k)

/-- Second map: MachineRed → ParRedStar (M-2, moved here from
    `RcicMachineSound` so the typed slice — which deliberately avoids the
    legacy `RcicParRedSR` import chain — can reach it. Same FQN:
    `Rcic.Machine.machineRed_toParRedStar`). -/
def machineRed_toParRedStar {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat}→ MachineRed E n Γ a b → ParRedStar E n Γ a b
  | _, _, _, .refl Γ e => .refl Γ e
  | _, _, _, .headBeta Γ A body arg rest k =>
      .tail
        (parRed_foldApps_congr (parRedArgs_refl rest)
          (.beta Γ A A body body arg arg (.refl Γ A)
            (.refl (LocalDecl.assumption A :: Γ) body)
            (.refl Γ arg)))
        (machineRed_toParRedStar k)
  | _, _, _, .headZeta Γ A value body rest k =>
      .tail
        (parRed_foldApps_congr (parRedArgs_refl rest)
          (.zeta Γ A A value value body body (.refl Γ A)
            (.refl Γ value)
            (.refl (LocalDecl.letBinding A value :: Γ) body)))
        (machineRed_toParRedStar k)
  | _, _, _, .headDelta Γ r ls m b rest hres hbody htr k =>
      .tail
        (parRed_foldApps_congr (parRedArgs_refl rest)
          (.delta Γ r ls m b hres hbody htr))
        (machineRed_toParRedStar k)

/-! ## Head normality and whnfCert (M-2 continued) -/

/-- Head-normality readout. -/
def machineWhnfDone (E : ResolvedEnv) (e : Expr Nat) : Bool :=
  match appsSpine e with
  | (.lam _ _, []) => true
  | (.lam _ _, _ :: _) => false
  | (.letE _ _ _, _) => false
  | (.lit _, _) => false
  | (.const r _, _) =>
      match E.members r with
      | some m => !(transparent m.mclass && m.body.isSome)
      | none => true
  | (_, _) => true

/-- WHNF certifier (M-2, fuel structural at top level — E-P2-2). -/
def whnfCert (E : ResolvedEnv) (n : Nat) :
    (fuel : Nat) → (Γ : LCtx) → (e : Expr Nat) →
    Cert (Σ' (w : Expr Nat), MachineRed E n Γ e w)
  | 0, Γ, e =>
      match appsSpine e with
      | (.lit _, _) => .no "[rcic_whnf_unknown_ctor]"
      | _ =>
          if machineWhnfDone E e then .ok ⟨e, .refl Γ e⟩
          else .no "[rcic_whnf_fuel]"
  | f + 1, Γ, e =>
    match hs : appsSpine e with
    | (.lam A body, arg :: rest) =>
        match whnfCert E n f Γ (foldApps (instantiate0 arg body) rest) with
        | .no msg => Cert.no msg
        | .ok ⟨w, k⟩ =>
            .ok ⟨w, machineSpineEq hs ▸ MachineRed.headBeta Γ A body arg rest k⟩
    | (.letE A value body, rest) =>
        match whnfCert E n f Γ (foldApps (instantiate0 value body) rest) with
        | .no msg => Cert.no msg
        | .ok ⟨w, k⟩ =>
            .ok ⟨w, machineSpineEq hs ▸ MachineRed.headZeta Γ A value body rest k⟩
    | (.lit _, _) => .no "[rcic_whnf_unknown_ctor]"
    | (.const r ls, rest) =>
        match hm : E.members r with
        | none => .ok ⟨e, .refl Γ e⟩
        | some m =>
            match hb : m.body, htr : transparent m.mclass with
            | some b, true =>
                match whnfCert E n f Γ (foldApps (instantiateLevels ls b) rest) with
                | .no msg => Cert.no msg
                | .ok ⟨w, k⟩ =>
                    .ok ⟨w, machineSpineEq hs ▸
                      MachineRed.headDelta Γ r ls m b rest hm hb htr k⟩
            | _, _ => .ok ⟨e, .refl Γ e⟩
    | (_, _) => .ok ⟨e, .refl Γ e⟩

/-! ## M-4: Conversion certifier — 03 §13's ordered algorithm -/

/-- Mismatch-pending decision (RULING O, RULING P). -/
def convMismatchResidue (A l r : Expr Nat) : String :=
  match A, l, r with
  | .sort .zero, _, _ => "[rcic_conv_irrelevance_out_of_slice]"
  | _, .lam _ _, .lam _ _ => "[rcic_conv_eta_out_of_slice]"
  | _, _, _ => "[rcic_conv_mismatch]"

--
-- M-4: Conversion certifier — 03 §13's ordered algorithm
-- Tactic-mode definition to handle the dependent-type chaining.
-- The `.app`/`.app` arm is the kernel-faithful `Conv.app` congruence:
-- it is strictly monotone over the former catch-all (it can only
-- turn that arm's `.no` into a derivation-carrying `.ok`).
--
def convCert (E : ResolvedEnv) (n : Nat) :
    (fuel : Nat) → (Γ : LCtx) → (A l r : Expr Nat) →
    Cert (Conv E n Γ l r)
  | 0, Γ, A, l, r => .no "[rcic_conv_fuel]"
  | f + 1, Γ, A, l, r => by
    -- Step 1: syntax equality
    if hlr : l = r then
      exact hlr ▸ Cert.ok (.refl Γ l)
    else
      -- Step 3: whnf both sides
      match hwl : whnfCert E n f Γ l with
      | .no msg => exact Cert.no msg
      | .ok ⟨wl, kl⟩ =>
        match hwr : whnfCert E n f Γ r with
        | .no msg => exact Cert.no msg
        | .ok ⟨wr, kr⟩ =>
          -- Step 4: structural comparison of whnf'd heads
          if hwleq : wl = wr then
            -- l ↝ wl = wr ↝ r → l ≈ r by trans·symm
            exact Cert.ok (.trans Γ l wl r
              (machineRed_toConv kl)
              (.trans Γ wl wr r
                (hwleq ▸ (.refl Γ wl : Conv E n Γ wl wl))
                (.symm Γ r wr (machineRed_toConv kr))))
          else
            -- Steps 5-9: head-level comparison (sorts, consts, congruence)
            match wl, wr with
            | .sort u, .sort v =>
              if huv : u = v then
                exact Cert.ok (.trans Γ l (.sort u) r
                  (machineRed_toConv kl)
                  (.trans Γ (.sort u) (.sort v) r
                    (.sorts Γ u v (huv ▸ machineEqN_refl u))
                    (.symm Γ r (.sort v) (machineRed_toConv kr))))
              else
                exact Cert.no (convMismatchResidue A l r)
            | .const r₁ ls₁, .const r₂ ls₂ =>
              if hconj : r₁ = r₂ ∧ ls₁ = ls₂ then
                exact Cert.ok (.trans Γ l (.const r₁ ls₁) r
                  (machineRed_toConv kl)
                  (.trans Γ (.const r₁ ls₁) (.const r₂ ls₂) r
                    (hconj.1 ▸ hconj.2 ▸ (.consts Γ r₁ ls₁ ls₁ (machineEqNList_refl ls₁)))
                    (.symm Γ r (.const r₂ ls₂) (machineRed_toConv kr))))
              else
                exact Cert.no (convMismatchResidue A l r)
            | .app f₁ a₁, .app f₂ a₂ =>
                -- Application congruence (kernel's `Conv.app`):
                -- compare function- and argument-parts recursively.
                -- Each subcall whnfs its own side, so a δ step under
                -- an argument (e.g. `i64Ref ↦ mkRef …` inside
                -- `CCT · ·`) is reached here. Monotone: the arm only
                -- ever turns this match's former `.no` into a
                -- derivation-carrying `.ok`; a subcall refusal is
                -- re-labelled by the match's own residue so that
                -- `convAt` still lands `accepted .conversionMismatch`
                -- (not `.refused [rcic_conv_eta_out_of_slice]` /
                -- `[rcic_conv_fuel]`) — the catch-all's pre-arm answer.
                match convCert E n f Γ A f₁ f₂ with
                | .no _ => exact Cert.no (convMismatchResidue A l r)
                | .ok hf =>
                    match convCert E n f Γ A a₁ a₂ with
                    | .no _ => exact Cert.no (convMismatchResidue A l r)
                    | .ok ha =>
                        exact Cert.ok (.trans Γ l (.app f₁ a₁) r
                          (machineRed_toConv kl)
                          (.trans Γ (.app f₁ a₁) (.app f₂ a₂) r
                            (.app Γ f₁ f₂ a₁ a₂ hf ha)
                            (.symm Γ r (.app f₂ a₂) (machineRed_toConv kr))))
            | _, _ =>
              exact Cert.no (convMismatchResidue A l r)

/-! ## M-5: Infer certifier — 03 §10, one dispatch per head -/

/-- Level well-formedness for HasTy.const — vacuous for [] (M-5).
ATTEMPT 1 (2026-09-05): direct case split — the cons arm at n = 0 is
NOT provable for arbitrary levels (eval of Level.zero is some 0).
ATTEMPT 2 (CLOSED): carry the `ls = []` branch proof from the only
caller (inferCert's `hls`); the obligation is then vacuous by
`List.not_mem_nil`. -/
def hwf_of_ls (n : Nat) (ls : List Level) (hls : ls = []) :
    ∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n := by
  subst hls
  intro l hl
  exact absurd hl (List.not_mem_nil l)

/-- Infer certifier — 03 §10, fuel structural. -/
def inferCert (E : ResolvedEnv) (n : Nat) :
    (fuel : Nat) → (Γ : LCtx) → (e : Expr Nat) →
    Cert (Σ' (T : Expr Nat), HasTy E n Γ e T)
  | 0, Γ, e =>
      match e with
      | .lit _ => .no "[rcic_infer_unknown_ctor]"
      | _ => .no "[rcic_infer_fuel]"
  | f + 1, Γ, e =>
    match e with
    | .lit _ => .no "[rcic_infer_unknown_ctor]"
    | .bvar i =>
        match hlt : lookupType Γ i with
        | some A => .ok ⟨A, .bvar Γ i A hlt⟩
        | none => .no "[rcic_pi_check_bvar_unbound]"
    | .sort l =>
        .ok ⟨.sort (.succ l), .sort Γ l⟩
    | .const r ls =>
        if hls : ls = [] then
          match hm : E.members r with
          | some m =>
              if h0 : (0 : Nat) = m.arity then
                .ok ⟨instantiateLevels ls m.mtype,
                  .const Γ r ls m hm (hls ▸ h0 ▸ (rfl : ([] : List Level).length = 0)) (hwf_of_ls n ls hls)⟩
              else .no ImportLevel.constLevelResidue
          | none => .no "[rcic_lookup_group_not_found]"
        else if hadmit : ImportLevel.constLevelsAdmitted n ls = true then
          -- `levelBounded` at `n > 0`, except exactly `.succ .zero`.
          -- Arity 0 and `.succ .zero` stay the same residue, before lookup.
          match hm : E.members r with
          | some m =>
              if hlen : ls.length = m.arity then
                .ok ⟨instantiateLevels ls m.mtype,
                  .const Γ r ls m hm hlen
                    (ImportLevel.constLevels_hwf hadmit)⟩
              else .no ImportLevel.constLevelResidue
          | none => .no "[rcic_lookup_group_not_found]"
        else .no ImportLevel.constLevelResidue
    | .pi A B =>
        match inferCert E n f Γ A with
        | .no msg => Cert.no msg
        | .ok ⟨TA, hA⟩ =>
            match TA with
            | .sort u =>
                match inferCert E n f (LocalDecl.assumption A :: Γ) B with
                | .no msg => Cert.no msg
                | .ok ⟨TB, hB⟩ =>
                    match TB with
                    | .sort v => .ok ⟨.sort (.imax u v), .pi Γ A u B v hA hB⟩
                    | _ => .no "[rcic_infer_not_a_sort]"
            | _ => .no "[rcic_infer_not_a_sort]"
    | .lam A body =>
        match inferCert E n f Γ A with
        | .no msg => Cert.no msg
        | .ok ⟨TA, hA⟩ =>
            match TA with
            | .sort u =>
                match inferCert E n f (LocalDecl.assumption A :: Γ) body with
                | .no msg => Cert.no msg
                | .ok ⟨Tbody, hbody⟩ =>
                    .ok ⟨.pi A Tbody, .lam Γ A u body Tbody hA hbody⟩
            | _ => .no "[rcic_infer_not_a_sort]"
    | .app fn arg =>
        match inferCert E n f Γ fn with
        | .no msg => Cert.no msg
        | .ok ⟨Tf, hfn⟩ =>
            match whnfCert E n f Γ Tf with
            | .no msg => Cert.no msg
            | .ok ⟨Tfw, kfn⟩ =>
                -- M-5 Application: decompose the WHNF'd type (delta may
                -- be needed to expose the Π — infer-full row 1); the
                -- raw Tf is only the inferred syntactic type.
                let hfn' : HasTy E n Γ fn Tfw :=
                  .conv Γ fn Tf Tfw hfn (machineRed_toConv kfn)
                match inferCert E n f Γ arg with
                | .no msg => Cert.no msg
                | .ok ⟨Targ, harg⟩ =>
                    inferCert_app E n f Γ fn arg Tfw hfn' Targ harg
    | .letE A value body =>
        match inferCert E n f Γ A with
        | .no msg => Cert.no msg
        | .ok ⟨TA, hA⟩ =>
            match TA with
            | .sort u =>
                match inferCert E n f Γ value with
                | .no msg => Cert.no msg
                | .ok ⟨Tval, hval⟩ =>
                    match convCert E n f Γ A Tval A with
                    | .no msg => Cert.no msg
                    | .ok hc =>
                        match inferCert E n f (LocalDecl.letBinding A value :: Γ) body with
                        | .no msg => Cert.no msg
                        | .ok ⟨Tbody, hbody⟩ =>
                            .ok ⟨instantiate0 value Tbody, .letE Γ A u value Tbody hA (.conv Γ value Tval A hval hc) hbody⟩
            | _ => .no "[rcic_infer_not_a_sort]"
where
  field_of_pi (T : Expr Nat) : Expr Nat :=
    match T with
    | .pi _ B => B
    | _ => .sort .zero
  inferCert_app (E : ResolvedEnv) (n : Nat) (f : Nat) (Γ : LCtx)
      (fn arg Tf : Expr Nat) (hfn : HasTy E n Γ fn Tf)
      (Targ : Expr Nat) (harg : HasTy E n Γ arg Targ) :
      Cert (Σ' (T : Expr Nat), HasTy E n Γ (.app fn arg) T) :=
    match Tf with
    | .pi A B =>
        match convCert E n f Γ A Targ A with
        | .no msg => Cert.no msg
        | .ok hc =>
            .ok ⟨instantiate0 arg B, .app Γ fn arg A B hfn (.conv Γ arg Targ A harg hc)⟩
    | _ => .no "[rcic_infer_not_a_pi]"

/-! ## M-6: Check certifier — 03 §11's three-line path -/

/-- Check certifier: ensure expected is a sort, infer, convert. -/
def checkCert (E : ResolvedEnv) (n : Nat) :
    (fuel : Nat) → (Γ : LCtx) → (e A : Expr Nat) →
    Cert (HasTy E n Γ e A)
  | 0, Γ, e, A => .no "[rcic_pi_check_fuel]"
  | f + 1, Γ, e, A =>
      match inferCert E n f Γ A with
      | .no msg => Cert.no msg
      | .ok ⟨TA, hA⟩ =>
          match TA with
          | .sort _ =>
              match inferCert E n f Γ e with
              | .no msg => Cert.no msg
              | .ok ⟨Te, he⟩ =>
                  match convCert E n f Γ A Te A with
                  | .no msg => Cert.no msg
                  | .ok hc => Cert.ok (.conv Γ e Te A he hc)
          | _ => .no "[rcic_pi_check_not_a_sort]"

/-! ## M-8: kernelStepRaw — the encoding function -/

def kernelStepRaw (s : RawState) : StepOutcome :=
  match s.budget with
  | 0 => .result .suspended
  | _ + 1 =>
    match s.task with
    | .syntaxEqual a b =>
        if a = b then .result (.accepted .conversionConfirmed)
        else .result (.accepted .conversionMismatch)
    | .levelEqual l1 l2 =>
        -- H-11/H-11b: arm is landed FINAL decEqN
        -- (R-LevelNone). T3 MISMATCH on this arm
        -- permitted by Annex 23 23.H.11 (3).
        -- Import graph (measured): RcicMachine →
        -- Declarative, DTMeta, LevelDec;
        -- LevelDec → LevelZero → Declarative; no cycle.
        if decEqN l1 l2 then
          .result (.accepted .conversionConfirmed)
        else
          .result (.refused "[rcic_level_not_equal]")
    | .lookupLocal i =>
        match lookupType s.ambient.ctx i with
        | some A => .result (.accepted (.inferredType A))
        | none => .result (.refused "[rcic_pi_check_bvar_unbound]")
    | .lookupDeclaration r ls =>
        -- RM013: a nonempty list is still refused before resolution.
        -- `infer` is the arm that admits `param i` with `i < univs`.
        if ls = [] then
          match inferCert s.ambient.env s.ambient.univs s.budget
              s.ambient.ctx (.const r ls) with
          | .ok ⟨T, _⟩ => .result (.accepted (.inferredType T))
          | .no msg => .result (.refused msg)
        else
          .result (.refused ImportLevel.constLevelResidue)
    | .whnfAt A e =>
        match whnfCert s.ambient.env s.ambient.univs s.budget
            s.ambient.ctx e with
        | .ok ⟨w, _⟩ => .result (.accepted (.inferredWhnf A w))
        | .no msg => .result (.refused msg)
    | .convAt A l r =>
        match convCert s.ambient.env s.ambient.univs s.budget
            s.ambient.ctx A l r with
        | .ok _ => .result (.accepted .conversionConfirmed)
        | .no msg =>
            if msg = "[rcic_conv_mismatch]" then
              .result (.accepted .conversionMismatch)
            else .result (.refused msg)
    | .infer e =>
        match inferCert s.ambient.env s.ambient.univs s.budget
            s.ambient.ctx e with
        | .ok ⟨T, _⟩ => .result (.accepted (.inferredType T))
        | .no msg => .result (.refused msg)
    | .check e A =>
        match checkCert s.ambient.env s.ambient.univs s.budget
            s.ambient.ctx e A with
        | .ok _ => .result (.accepted .checked)
        | .no msg => .result (.refused msg)
    | .convType _ _ => .result (.refused "[machine_task_not_implemented]")

def runRaw : Nat → RawState → RunResult
  | 0, _ => .suspended
  | k + 1, s =>
    match kernelStepRaw s with
    | .step s' => runRaw k s'
    | .result r => r

/-! ## Surviving RM* theorems (M-1 re-proofs) -/

theorem RM001_deterministic (s : RawState) (r1 r2 : StepOutcome)
    (h1 : kernelStepRaw s = r1) (h2 : kernelStepRaw s = r2) : r1 = r2 := by
  subst h1; subst h2; rfl

theorem RM002_locally_bounded (s : RawState) (s' : RawState)
    (h : kernelStepRaw s = .step s') : s'.budget < s.budget := by
  exfalso
  cases hb : s.budget <;> cases ht : s.task <;>
    simp only [kernelStepRaw, hb, ht] at h <;>
    (try split at h) <;> (try split at h) <;>
    first | exact h | nomatch h | omega

theorem RM004_zero_suspends (s : RawState) :
    runRaw 0 s = .suspended := rfl

theorem RM005_accepted_stable (k : Nat) (s : RawState) (p : AcceptedPayload)
    (h : runRaw k s = .accepted p) :
    runRaw (k + 1) s = .accepted p := by
  cases k with
  | zero => simp only [runRaw] at h; nomatch h
  | succ k' =>
    simp only [runRaw] at h ⊢
    cases hkr : kernelStepRaw s with
    | step s'' =>
      exfalso
      cases hb : s.budget <;> cases ht : s.task <;>
        simp only [kernelStepRaw, hb, ht] at hkr <;>
        (try split at hkr) <;> (try split at hkr) <;>
        first | exact hkr | nomatch hkr | omega
    | result r =>
      simp only [hkr] at h ⊢
      exact h

theorem RM006_refused_stable (k : Nat) (s : RawState) (r : String)
    (h : runRaw k s = .refused r) :
    runRaw (k + 1) s = .refused r := by
  cases k with
  | zero => simp only [runRaw] at h; nomatch h
  | succ k' =>
    simp only [runRaw] at h ⊢
    cases hkr : kernelStepRaw s with
    | step s'' =>
      exfalso
      cases hb : s.budget <;> cases ht : s.task <;>
        simp only [kernelStepRaw, hb, ht] at hkr <;>
        (try split at hkr) <;> (try split at hkr) <;>
        first | exact hkr | nomatch hkr | omega
    | result r' =>
      simp only [hkr] at h ⊢
      exact h

theorem RM008_zero_suspension_exact (s : RawState) :
    runRaw 0 s = .suspended := rfl

theorem kernelStepRaw_never_step (s : RawState) (s' : RawState) :
    kernelStepRaw s ≠ .step s' := by
  intro h
  cases hb : s.budget <;> cases ht : s.task <;>
    simp only [kernelStepRaw, hb, ht] at h <;>
    (try split at h) <;> (try split at h) <;>
    first | exact h | nomatch h | omega

theorem RM003_landed_no_step_to_preserve (s : RawState) (s' : RawState)
    (h : kernelStepRaw s = .step s') : False :=
  kernelStepRaw_never_step s s' h

theorem RM004_landed_oneshot (s : RawState) :
    (∃ r, kernelStepRaw s = .result r) ∨ kernelStepRaw s = .result .suspended := by
  cases hb : s.budget <;> cases ht : s.task <;>
    simp only [kernelStepRaw, hb, ht] <;>
    (try split) <;> (try split) <;>
    first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr rfl

theorem RM007_no_integrity_producer (s : RawState) (res : String) :
    kernelStepRaw s ≠ .result (.integrity res) := by
  intro h
  cases hb : s.budget <;> cases ht : s.task <;>
    simp only [kernelStepRaw, hb, ht] at h <;>
    (try split at h) <;> (try split at h) <;>
    first | exact h | nomatch h | omega

theorem RM007_runRaw_three_ctors (k : Nat) (s : RawState) :
    (∃ p, runRaw k s = .accepted p)
    ∨ (∃ r, runRaw k s = .refused r)
    ∨ runRaw k s = .suspended := by
  cases k with
  | zero => exact Or.inr (Or.inr rfl)
  | succ k' =>
    simp only [runRaw]
    cases hkr : kernelStepRaw s with
    | step s'' =>
      exfalso
      exact kernelStepRaw_never_step s s'' hkr
    | result r =>
      cases r with
      | accepted p => exact Or.inl ⟨p, rfl⟩
      | refused r' => exact Or.inr (Or.inl ⟨r', rfl⟩)
      | integrity res =>
          exfalso
          exact RM007_no_integrity_producer s res hkr
      | suspended => exact Or.inr (Or.inr rfl)

theorem RM007_runRaw_four_ctors (k : Nat) (s : RawState) :
    (∃ p, runRaw k s = .accepted p)
    ∨ (∃ r, runRaw k s = .refused r)
    ∨ (∃ r, runRaw k s = .integrity r)
    ∨ runRaw k s = .suspended := by
  cases k with
  | zero => exact Or.inr (Or.inr (Or.inr rfl))
  | succ k' =>
    simp only [runRaw]
    cases hkr : kernelStepRaw s with
    | step s'' =>
      exfalso
      exact kernelStepRaw_never_step s s'' hkr
    | result r =>
      cases r with
      | accepted p => exact Or.inl ⟨p, rfl⟩
      | refused r' => exact Or.inr (Or.inl ⟨r', rfl⟩)
      | integrity res => exact Or.inr (Or.inr (Or.inl ⟨res, rfl⟩))
      | suspended => exact Or.inr (Or.inr (Or.inr rfl))

theorem RM_syntaxEqual_whole_ast (amb : Ambient) (a b : Expr Nat) :
    kernelStepRaw ⟨amb, .syntaxEqual a b, 1⟩
      = .result (if a = b then .accepted .conversionConfirmed
          else .accepted .conversionMismatch) := by
  by_cases hab : a = b
  · simp only [kernelStepRaw, if_pos hab]
  · simp only [kernelStepRaw, if_neg hab]

/-! ## RM-011 (RULING L gap compiled as sealed type-④ refutations) -/

theorem RM011_param0_ne_param1 : ¬ eqN (.param 0) (.param 1) := by
  intro h
  have h0 := h (fun i => if i = 0 then some 0 else some 1)
  simp only [eval] at h0
  -- h0 : (if True then some 0 else some 1) = if 1 = 0 then some 0
  -- else some 1 (rule 3, attempt 2: explicit ite splits)
  split at h0
  · split at h0
    · next h10 => exact absurd h10 (by omega)
    · exact absurd h0 (by intro hc; cases hc)
  · next hf => exact hf trivial

/- RETIRED (H-11, R-Retire): dummy-arm refutations about
the replaced `eval (fun _ => some 0)` arm. Text kept,
not compiled. Names move to `retiredTheorems`. Reason:
arm replaced by `decEqN` (H-11). Not weakened.
  theorem RM011_landed_accepts_unequal_params
      (amb : Ambient) :
      kernelStepRaw ⟨amb,
        .levelEqual (.param 0) (.param 1), 1⟩
        = .result (.accepted .conversionConfirmed) := by
    rfl
  theorem RM011_landed_not_eqN (amb : Ambient) :
      kernelStepRaw ⟨amb,
        .levelEqual (.param 0) (.param 1), 1⟩
        = .result (.accepted .conversionConfirmed)
      ∧ ¬ eqN (.param 0) (.param 1) :=
    ⟨RM011_landed_accepts_unequal_params amb,
      RM011_param0_ne_param1⟩
-/

/-- RM-011: accepted `levelEqual` implies `eqN`
(`03` §15 "level equality sound"; `02` §2 `=ₙ`;
DT-026 via `decEqN_sound`). -/
theorem RM011_levelEqual_sound
    (amb : Ambient) (l1 l2 : Level) (b : Nat)
    (hacc : kernelStepRaw
      ⟨amb, .levelEqual l1 l2, b⟩
      = .result (.accepted .conversionConfirmed)) :
    eqN l1 l2 := by
  cases b with
  | zero =>
      simp only [kernelStepRaw] at hacc
      exact nomatch hacc
  | succ _ =>
      cases hdec : decEqN l1 l2 with
      | true =>
          exact decEqN_sound l1 l2 hdec
      | false =>
          simp only [kernelStepRaw, hdec] at hacc
          exact nomatch hacc

/-- M-005: param 0 vs param 1 REFUSED. -/
theorem RM011_param0_param1_refused
    (amb : Ambient) :
    kernelStepRaw ⟨amb,
      .levelEqual (.param 0) (.param 1), 1⟩
      = .result (.refused "[rcic_level_not_equal]") := by
  simp only [kernelStepRaw, m005_param_dec]
  have h : ¬ (false = true) := fun c =>
    Bool.noConfusion c
  simp only [if_neg h]

/-- M-005: `imax 1 0` vs `0` ACCEPTED
(landed equal-by-imax; H-6h `imax 1 u` vs `u`
is NOT accepted by this tree's `decEqN`). -/
theorem RM011_imax_zero_accepted
    (amb : Ambient) :
    kernelStepRaw ⟨amb,
      .levelEqual
        (.imax (.succ .zero) .zero) .zero, 1⟩
      = .result (.accepted .conversionConfirmed) := by
  simp only [kernelStepRaw, m005_imax_dec]
  simp only [if_pos True.intro]

/-- RM-011: `eqN` implies accepted `levelEqual`
(`03` §15 completeness half; `02` §2 `=ₙ`;
DT-026 via `decEqN_complete`). Budget is
`Nat.succ b` because `kernelStepRaw` at 0
suspends (the arm is not reached). -/
theorem RM011_levelEqual_complete
    (amb : Ambient) (l1 l2 : Level) (b : Nat)
    (heq : eqN l1 l2) :
    kernelStepRaw
      ⟨amb, .levelEqual l1 l2, Nat.succ b⟩
      = .result (.accepted .conversionConfirmed) := by
  have hdec : decEqN l1 l2 = true :=
    decEqN_complete l1 l2 heq
  simp only [kernelStepRaw, hdec]
  simp only [if_pos True.intro]

/-- M-005: `imax 1 (param 0)` vs `param 0`
ACCEPTED (H-6h; R-LevelNone final decider). -/
theorem RM011_imax_param_accepted
    (amb : Ambient) :
    kernelStepRaw ⟨amb,
      .levelEqual
        (.imax (.succ .zero) (.param 0))
        (.param 0), 1⟩
      = .result (.accepted .conversionConfirmed) := by
  have hdec :
      decEqN
        (.imax (.succ .zero) (.param 0))
        (.param 0) = true := rfl
  simp only [kernelStepRaw, hdec]
  simp only [if_pos True.intro]

/-! ## RM-012: local lookup (re-stated over P-1/P-2) -/

theorem RM012_lookupLocal_accepted (s : RawState) (i : Nat)
    (A : Expr Nat) (htask : s.task = .lookupLocal i)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType A))) :
    lookupType s.ambient.ctx i = some A ∧ 0 < s.budget := by
  constructor
  · cases hb : s.budget with
    | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
    | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next A' heq =>
          simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
            AcceptedPayload.inferredType.injEq] at hacc
          exact heq.trans (congrArg some hacc)
      · nomatch hacc
  · cases hb : s.budget with
    | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
    | succ b => omega

def RM012_lookupLocal_hasTy (s : RawState) (i : Nat)
    (A : Expr Nat) (htask : s.task = .lookupLocal i)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType A))) :
    HasTy s.ambient.env s.ambient.univs s.ambient.ctx (.bvar i) A := by
  have ⟨hlk, _⟩ := RM012_lookupLocal_accepted s i A htask hacc
  exact .bvar _ i A hlk

/-! ## RM-013: declaration lookup -/

def RM013_lookupDeclaration_resolved (s : RawState) (r : Nat)
    (ls : List Level) (T : Expr Nat)
    (htask : s.task = .lookupDeclaration r ls)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType T))) :
    Σ' (m : CheckedMember),
      (ls = []) ×'
      (s.ambient.env.members r = some m) ×'
      (0 = m.arity) ×'
      (T = instantiateLevels ls m.mtype) := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      -- Nonempty `ls` is refused before `inferCert`. The remaining
      -- `ls = []` branch is the arity-0 arm; `hlsOuter` reduces the
      -- inner `if hls : ls = []` before the member split.
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next hlsOuter =>
          simp only [inferCert] at hacc
          split at hacc
          · next T' hty heq =>
              have hT : T' = T := by
                simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
                  AcceptedPayload.inferredType.injEq] at hacc
                exact hacc
              -- `hlsOuter` does not reduce this `dite`; split it.
              -- The nonempty arm contradicts `hlsOuter`.
              split at heq
              · next hls =>
                  split at heq
                  · next m hm =>
                      split at heq
                      · next h0 =>
                          simp only [Cert.ok.injEq] at heq
                          have hTm : instantiateLevels ls m.mtype = T' := by
                            cases heq; rfl
                          exact ⟨m, hls, hm, h0, (hTm.trans hT).symm⟩
                      · nomatch heq
                  · nomatch heq
              · next hnot =>
                  exact absurd hlsOuter hnot
          · nomatch hacc
      · nomatch hacc

def RM013_lookupDeclaration_hasTy (s : RawState) (r : Nat)
    (ls : List Level) (T : Expr Nat)
    (htask : s.task = .lookupDeclaration r ls)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType T))) :
    HasTy s.ambient.env s.ambient.univs s.ambient.ctx (.const r ls) T := by
  have ⟨m, hls, hm, h0, hT⟩ := RM013_lookupDeclaration_resolved s r ls T htask hacc
  have hlen : ls.length = m.arity := by
    subst hls; simp only [List.length_nil]; exact h0
  exact hT ▸ .const s.ambient.ctx r ls m hm hlen (hwf_of_ls s.ambient.univs ls hls)

/-! ## §7 type-④ exhibits (MR-5: whole-term operations in one call) -/

theorem RM002_whnf_whole_term (amb : Ambient) :
    kernelStepRaw ⟨amb,
        .whnfAt (.sort .zero)
          (.app (.app (.lam (.sort .zero)
              (.lam (.sort .zero) (.bvar 1))) (.sort .zero))
            (.sort .zero)), 2⟩
      = .result (.accepted (.inferredWhnf (.sort .zero) (.sort .zero))) := by
  rfl

theorem RM002_conv_whole_term (amb : Ambient) :
    kernelStepRaw ⟨amb,
        .convAt (.sort (.succ .zero))
          (.app (.app (.lam (.sort .zero)
              (.lam (.sort .zero) (.bvar 1))) (.sort .zero))
            (.sort .zero))
          (.sort .zero), 3⟩
      = .result (.accepted .conversionConfirmed) := by
  rfl

theorem RM002_infer_whole_term (E : ResolvedEnv) (n : Nat) :
    kernelStepRaw ⟨⟨E, n, []⟩,
        .infer (.app (.lam (.sort (.succ .zero)) (.bvar 0))
          (.sort .zero)), 3⟩
      = .result (.accepted (.inferredType (.sort (.succ .zero)))) := by
  rfl

/-! ## RM-017 convType armless (C-4: stays) -/

theorem RM017_convType_refused_unimplemented (A B : Expr Nat) (amb : Ambient) :
    kernelStepRaw ⟨amb, .convType A B, 1⟩
      = .result (.refused "[machine_task_not_implemented]") := by
  rfl

theorem RM017_convType_never_accepted (A B : Expr Nat) (p : AcceptedPayload) (amb : Ambient) :
    kernelStepRaw ⟨amb, .convType A B, 1⟩
      ≠ .result (.accepted p) := by
  intro h
  cases h

/-! ## Batch-B positive pins (withdrawal replacements) -/

/-- RM-014 reduces: the accepted whnf payload CARRIES the MachineRed
chain (extracted from whnfCert's Cert.ok sigma). -/
def RM014_whnf_reduces (s : RawState) (A e w : Expr Nat)
    (htask : s.task = .whnfAt A e)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    MachineRed s.ambient.env s.ambient.univs s.ambient.ctx e w := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next w' kred _heq =>
          have hw : w' = w := by
            simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
              AcceptedPayload.inferredWhnf.injEq] at hacc
            exact hacc.2
          subst hw
          exact kred
      · nomatch hacc

/-- RULING W (Annex 21, #3825): the head-normal closure, stated on the
CERTIFICATE `c` and concluding on `c.1` — the `machineSpineEq ▸` cast
lives in `c.2` and is never inspected. Arm discipline mirrors
`whnfCert`'s definition arm for arm (attempt 1's statement-on-⟨w,k⟩
shape is what made the IH inapplicable; this is attempt 2's shape). -/
theorem whnfCert_ok_done (E : ResolvedEnv) (n : Nat) :
    ∀ (fuel : Nat) (Γ : LCtx) (e : Expr Nat)
      (c : Σ' (w : Expr Nat), MachineRed E n Γ e w),
    whnfCert E n fuel Γ e = .ok c → machineWhnfDone E c.1 = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro Γ e c h
      rw [whnfCert] at h
      cases hsp : appsSpine e with | mk hd args =>
      conv at h => rw [hsp]
      cases hd with
      | lit _ => cases h
      | _ =>
          -- hd is a non-lit constructor: the outer matcher iota-reduces
          -- to the ite; make that reduction definitional-by-change so
          -- split only has the ite left
          change (if machineWhnfDone E e then
              Cert.ok ⟨e, MachineRed.refl Γ e⟩
            else Cert.no "[rcic_whnf_fuel]") = Cert.ok c at h
          split at h
          · next hdone =>
              have h1 : c.1 = e := by cases h; rfl
              rw [h1]; exact hdone
          · cases h
  | succ f ih =>
      intro Γ e c h
      rw [whnfCert] at h
      -- the five definition patterns, one arm each (RULING W (ii))
      split at h
      · next A body arg rest hsp =>
          split at h
          · cases h
          · next w k hin =>
              have hd1 : c.1 = w := by cases h; rfl
              exact hd1 ▸ ih _ _ ⟨w, k⟩ hin
      · next A value body hsp =>
          split at h
          · cases h
          · next w k hin =>
              have hd1 : c.1 = w := by cases h; rfl
              exact hd1 ▸ ih _ _ ⟨w, k⟩ hin
      · cases h
      · next r ls hsp =>
          split at h
          · next hm =>
              have h1 : c.1 = e := by cases h; rfl
              rw [h1]
              simp only [machineWhnfDone, hsp, hm]
          · next m hm =>
              split at h
              · next b hb htr =>
                  split at h
                  · cases h
                  · next w k hin =>
                      have hd1 : c.1 = w := by cases h; rfl
                      exact hd1 ▸ ih _ _ ⟨w, k⟩ hin
              · next htr =>
                  have h1 : c.1 = e := by cases h; rfl
                  rw [h1]
                  simp only [machineWhnfDone, hsp, hm]
                  -- remaining: !(transparent && isSome) = true, from the
                  -- discrimination htr : ∀ b, body = some b → transp → False
                  cases hbody : m.body with
                  | none =>
                      simp only [hbody, Option.isSome_none, Bool.and_false]
                      rfl
                  | some b =>
                      cases htrb : transparent m.mclass with
                      | false =>
                          simp only [htrb, Bool.false_and]
                          rfl
                      | true => exact absurd (htr b hbody htrb) (by cases ·)
      · next hd args dlam dlet dlit dconst hsp =>
          -- split's discriminations: hd is not lam-with-cons / letE /
          -- lit / const (those are the earlier arms)
          have h1 : c.1 = e := by cases h; rfl
          rw [h1]
          cases hd with
          | lam A body =>
              cases args with
              | nil => simp only [machineWhnfDone, hsp]
              | cons arg rest => exact (dlam A body arg rest rfl rfl).elim
          | letE A value body => exact (dlet A value body rfl).elim
          | lit t => exact (dlit t rfl).elim
          | const r ls => exact (dconst r ls rfl).elim
          | _ => simp only [machineWhnfDone, hsp]

theorem RM014_whnf_head_normal (s : RawState) (A e w : Expr Nat)
    (htask : s.task = .whnfAt A e)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    machineWhnfDone s.ambient.env w = true := by
  have k := RM014_whnf_reduces s A e w htask hacc
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next w' kred heq =>
          have hw : w' = w := by
            simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
              AcceptedPayload.inferredWhnf.injEq] at hacc
            exact hacc.2
          subst hw
          exact whnfCert_ok_done _ _ _ _ _ ⟨w', kred⟩ heq
      · nomatch hacc

/-- RM-015 infer sound: the accepted infer payload carries its HasTy. -/
def RM015_infer_sound (s : RawState) (e T : Expr Nat)
    (htask : s.task = .infer e)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType T))) :
    HasTy s.ambient.env s.ambient.univs s.ambient.ctx e T := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next T' hty heq =>
          have hT : T' = T := by
            simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
              AcceptedPayload.inferredType.injEq] at hacc
            exact hacc
          subst hT
          exact hty
      · nomatch hacc

/-- RM-016 check sound: the accepted check payload carries its HasTy. -/
def RM016_check_sound (s : RawState) (e A : Expr Nat)
    (htask : s.task = .check e A)
    (hacc : kernelStepRaw s = .result (.accepted .checked)) :
    HasTy s.ambient.env s.ambient.univs s.ambient.ctx e A := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next hty _heq => exact hty
      · nomatch hacc

/-- RM-016 run-level: runRaw's accepted check carries the one-step
HasTy (the .step case refuted by kernelStepRaw_never_step). -/
def RM016_run_check_sound (k : Nat) (s : RawState) (e A : Expr Nat)
    (htask : s.task = .check e A)
    (hacc : runRaw (k + 1) s = .accepted .checked) :
    HasTy s.ambient.env s.ambient.univs s.ambient.ctx e A := by
  simp only [runRaw] at hacc
  cases hkr : kernelStepRaw s with
  | step s' =>
      exact (kernelStepRaw_never_step s s' hkr).elim
  | result res =>
      rw [hkr] at hacc
      exact RM016_check_sound s e A htask
        (hkr.trans (congrArg StepOutcome.result hacc))

/-- RM-017 confirmed: the accepted convAt payload carries the Conv. -/
def RM017_conversion_confirmed (s : RawState) (A l r : Expr Nat)
    (htask : s.task = .convAt A l r)
    (hacc : kernelStepRaw s = .result (.accepted .conversionConfirmed)) :
    Conv s.ambient.env s.ambient.univs s.ambient.ctx l r := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · -- .ok: the payload discards the Conv; split still binds it
        next hc _heq => exact hc
      · split at hacc
        · -- mismatch ≠ confirmed: payload ctor clash
          nomatch hacc
        · nomatch hacc

/-! ## RM-018/019: out-of-slice refusals with closed literals -/

theorem RM018_irr_branch_refused (amb : Ambient) (k : Nat) :
    kernelStepRaw ⟨amb, .convAt (.sort .zero)
        (.sort (.succ .zero))
        (.sort (.succ (.succ .zero))), k + 1⟩
      = .result (.refused "[rcic_conv_irrelevance_out_of_slice]") := by
  -- D-34: two cases suffice; whnfCert's top-level Nat patterns (D-35)
  -- reduce at literal fuel and neither branch recurses on these heads
  cases k with
  | zero => rfl
  | succ k' => rfl

theorem RM019_eta_branch_refused (amb : Ambient) (k : Nat) :
    kernelStepRaw ⟨amb, .convAt (.sort (.succ .zero))
        (.lam (.sort .zero) (.bvar 0))
        (.lam (.sort .zero) (.sort .zero)), k + 2⟩
      = .result (.refused "[rcic_conv_eta_out_of_slice]") := by
  -- D-34, same shape as RM018
  cases k with
  | zero => rfl
  | succ k' => rfl

/-! ## RM-025: literal infer refused -/

theorem RM025_lit_infer_refused (amb : Ambient) (t k : Nat) :
    kernelStepRaw ⟨amb, .infer (.lit t), k + 1⟩
      = .result (.refused "[rcic_infer_unknown_ctor]") := by
  -- E-F03 (b), D-34's method, attempt 1: both the `_ + 1` arm of
  -- kernelStepRaw and inferCert's `f + 1` match reduce by iota on
  -- Nat.succ k, and `.lit t` hits the unknown-ctor arm in both fuel
  -- shapes — no split needed
  rfl

/-! ## Mismatch is not nonconvertibility (RULING O compiled statement) -/

theorem RM017_mismatch_is_not_nonconvertibility (amb : Ambient) :
    kernelStepRaw ⟨amb, .convAt (.sort (.succ (.succ .zero)))
        (.sort (.max .zero (.succ .zero)))
        (.sort (.succ .zero)), 1⟩
      = .result (.accepted .conversionMismatch)
    ∧ Nonempty (Conv amb.env amb.univs amb.ctx
        (.sort (.max .zero (.succ .zero)))
        (.sort (.succ .zero))) := by
  refine ⟨?_, ?_⟩
  -- budget is the literal 1: kernel reduction alone decides (D-34's
  -- discipline; no default-set simp inside a sealed name)
  · rfl
  · -- level eval agrees: max (eval 0) (eval 1) = eval 1, so the sorts
    -- are convertible through Conv.sorts (level eqN), not syntax.
    exact ⟨.sorts amb.ctx _ _ (fun _ => rfl)⟩

end Rcic.Machine
