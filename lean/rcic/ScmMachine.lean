/-
RCIC 06 §13–§15 — the INTRINSIC typed machine (K2 statement layer).

Owner text:
  §13 (06:245-256) `SCMControl Π T := eval Γ env (CoreExpr Π Γ T) |
      returning (CoreVal T) | raising (r) (CoreVal (PayloadType r)) | …`;
      "Typed frames and continuations ensure returned values resume only
      compatible control frames. An SCM configuration is a dependent pair of
      current result type, control, and typed continuation."
  §14 (06:260-274) `SCMFinal T := returned (CoreVal T) | raised (r)
      (CoreVal (PayloadType r))`, `SCMRunResult T := done (SCMFinal T) |
      suspended SCMConfig`; "There is no `none`, stuck, trap, or
      fuel-exhausted source outcome." "Raised control skips ordinary frames,
      skips nonmatching handlers, enters the first matching handler, or
      becomes a final raised outcome at an empty continuation."
  §15 (06:276-300) `SCMStep`, `scmStep`, `scmStep(c) = next c' ↔ SCMStep(c,c')`,
      `SCMRuns`, one local transition per step.

PIN (M-002a): `entryI` runs a carrier entry (form 2 of `rcic.scm_core`)
through `progCheck` (intrinsic bodies) → `toCoreVals` (intrinsic arguments)
→ `runI` on intrinsic configurations → erasure. Its 23 form-2 rows are
pinned in `ScmMachineIPins.lean` against the same corpus values as the raw
machine; so `Control`, `Frame`, `Cont`, `Config`, `Final`, `stepI`, `runI`
and the erasures are reachable from pinned rows.

TRANSCRIPTION TABLE (06 rule → Lean):
  §13 SCMControl: eval Γ env e → `Control.evalC`; returning → `Control.retC`;
        raising r (CoreVal (PayloadType r)) → `Control.raiseC` (payload
        typed by the catalog proof `h`); primitive / foldState / fixState →
        the primitive, fold and fix FRAMES (`primArgsF`, `foldL`/`foldI`,
        `fixI`/`fixL`/`fixS`/`fixT`): their state lives in the frame, the
        control is then `retC` or `evalC` — DEVIATION (layout), recorded:
        06 lists them as controls, the carrier holds them as frames and the
        pin follows the carrier
  §13 typed frames and continuations              → `Frame S A B`,
        `Cont S A T` (a frame takes a value of its hole type `A`)
  §13 configuration = dependent pair (type, control, continuation)
                                                  → `Config S T`
  §14 SCMFinal T                                   → `Final S T`
  §14 SCMRunResult T                               → `RunI S T` (`done` /
        `suspended`); the `integrity` arm is 06 §5's IntegrityResidue, a
        separate type from every source outcome (no `none`, stuck, trap,
        fuel-exhausted source outcome: there is no such constructor)
  §14 raised control skips ordinary frames / nonmatching handlers, enters
        the first matching handler, final at empty   → `raiseI`
  §15 scmStep                                      → `stepI`
  §15 SCMStep c c' := scmStep c = next c'          → `SCMStep`
  §15 scmStep(c) = final o ↔ c is a final configuration for o
                                                  → `IsFinalConfig`,
        theorem `Sim.stepI_final_iff`
  §13 last paragraph: "The first-order wire configuration stores closed tags
        and payloads. Its decoder reconstructs a raw configuration and
        validates the frame-chain typing before producing the typed semantic
        configuration." → NOT TRANSCRIBED (M-002b): no carrier decides the
        canonical configuration wire (#6029 K2 decision: the §17 core-wire
        family, control/frame tags as in rcic-scm-core); it is #6029 K3b.
        `Raw.Config` is the carrier's record form, not that wire
  §15 SCMRuns n c c'                               → `SCMRuns`
  §15 SCM-Cost-0: one unit per transition          → `runLoopI` counts
        `next` results
  §10 evaluation order                             → the push order of
        `evalI` / `retI` (same order as the raw machine, transition for
        transition)
  §12 negative limit raises negative_loop_bound; stop before exhausted
        limit before step; returns {converged, state, steps} → `fixL`/`fixS`
  06:218 fresh callee environment of exactly the arguments → `enterI`

RELATION TO THE EXISTING MINI-MODEL (#6029 K0, decided here): the bootstrap
chain's `lean/algorithms/SCMExecIntrinsicMWE.lean` (lit/var fragment, not in
`RcicFoundation`) is NOT merged into this root. Reason: its object is a strict
fragment of this file's `CoreExpr` / `stepI`, and the carrier it mirrors
(`apps/rcic-scm-exec`) is pinned by `ScmExec.lean` over that carrier's own
frame-chain wire. It is retired from the RCIC face — it carries no RCIC
statement and no seal entry — and left untouched in `BootstrapChain`, which
owns it.
-/
import rcic.ScmMachineRaw

namespace Rcic.Scm

/-! ## Lookups on typed environments, branches, records, bodies -/

def CoreVals.get : {Γ : List CoreTy} → {T : CoreTy} → CoreVals Γ → (i : Nat) → Γ.get? i = some T → CoreVal T
  | _ :: _, _, .cons x _, 0, h => (Option.some.inj h) ▸ x
  | _ :: _, _, .cons _ xs, n + 1, h => xs.get n h
  | [], _, .nil, _, h => nomatch h

def CoreVals.snoc : {ts : List CoreTy} → {A : CoreTy} → CoreVals ts → CoreVal A → CoreVals (ts ++ [A])
  | _, _, .nil, v => .cons v .nil
  | _, _, .cons x xs, v => .cons x (xs.snoc v)

def Branches.at {S : Sig} {Γ : List CoreTy} {T : CoreTy} : {ts : List CoreTy} → {A : CoreTy} →
    Branches S Γ ts T → (i : Nat) → ts.get? i = some A → CoreExpr S (A :: Γ) T
  | _ :: _, _, .cons b _, 0, h => (Option.some.inj h) ▸ b
  | _ :: _, _, .cons _ bs, n + 1, h => bs.at n h
  | [], _, .nil, _, h => nomatch h

def recordField : (fs : List (String × CoreTy)) → {k : String} → {A : CoreTy} →
    CoreVals (fs.map Prod.snd) → (i : Nat) → fs.get? i = some (k, A) → CoreVal A
  | (_, _) :: _, _, _, .cons x _, 0, h => (Prod.mk.inj (Option.some.inj h)).2 ▸ x
  | _ :: fs, _, _, .cons _ xs, n + 1, h => recordField fs xs n h
  | [], _, _, _, _, h => nomatch h

def Bodies.at {S : Sig} : {fs : List FnSig} → Bodies S fs → (i : Nat) → (f : FnSig) →
    fs.get? i = some f → CoreExpr S f.params f.result
  | _ :: _, .cons b _, 0, _, h => (Option.some.inj h) ▸ b
  | _ :: _, .cons _ bs, n + 1, f, h => bs.at n f h
  | [], .nil, _, _, h => nomatch h

/-! ## §13 Typed frames, continuations, controls, configurations -/

/-- The bounded-fix loop invariant carried by its frames: the semantic step
    count and the remaining limit stay within the i64 limit that started the
    loop (06 §12), so the returned `steps` field is always an i64. -/
def FixBound (left count : Int) : Prop := 0 ≤ count ∧ 0 ≤ left ∧ count + left ≤ i64Max

theorem fixBound_start {n : Int} (hn : inI64 n) (hlt : ¬ n < 0) : FixBound n 0 :=
  ⟨Int.le_refl 0, Int.not_lt.mp hlt, by rw [Int.zero_add]; exact hn.2⟩

theorem fixBound_inI64 {left count : Int} (hb : FixBound left count) : inI64 count :=
  ⟨Int.le_trans (show i64Min ≤ 0 by decide) hb.1, Int.le_trans (Int.le_add_of_nonneg_right hb.2.1) hb.2.2⟩

theorem fixBound_next {left count : Int} (hb : FixBound left count) (hz : ¬ left = 0) :
    FixBound (left - 1) (count + 1) :=
  have hpos : 0 < left := Int.lt_iff_le_and_ne.mpr ⟨hb.2.1, fun h => hz h.symm⟩
  have hsum : count + 1 + (left - 1) = count + left := by
    rw [Int.add_assoc, Int.add_comm 1 (left - 1), Int.sub_add_cancel]
  ⟨Int.le_trans hb.1 (Int.le_add_of_nonneg_right (show (0 : Int) ≤ 1 by decide)),
   Int.sub_nonneg_of_le (Int.lt_iff_add_one_le.mp hpos),
   hsum ▸ hb.2.2⟩

inductive Frame (S : Sig) : CoreTy → CoreTy → Type where
  | letF {Γ : List CoreTy} {A T : CoreTy} (env : CoreVals Γ) (b : CoreExpr S (A :: Γ) T) : Frame S A T
  | ifF {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) (th el : CoreExpr S Γ T) : Frame S .bool T
  | pairL {Γ : List CoreTy} {A B : CoreTy} (env : CoreVals Γ) (b : CoreExpr S Γ B) : Frame S A (.pair A B)
  | pairR {A B : CoreTy} (a : CoreVal A) : Frame S B (.pair A B)
  | fstF {A B : CoreTy} : Frame S (.pair A B) A
  | sndF {A B : CoreTy} : Frame S (.pair A B) B
  | injF {ts : List CoreTy} {A : CoreTy} (i : Nat) (h : ts.get? i = some A) : Frame S A (.sum ts)
  | matchF {Γ ts : List CoreTy} {T : CoreTy} (env : CoreVals Γ) (bs : Branches S Γ ts T) :
      Frame S (.sum ts) T
  | recF {Γ : List CoreTy} {A : CoreTy} (fs pre post : List (String × CoreTy)) (k : String)
      (heq : fs = pre ++ (k, A) :: post) (env : CoreVals Γ) (done : CoreVals (pre.map Prod.snd))
      (rest : Fields S Γ post) : Frame S A (.record fs)
  | fieldF {fs : List (String × CoreTy)} {A : CoreTy} (i : Nat) (k : String) (h : fs.get? i = some (k, A)) :
      Frame S (.record fs) A
  | consH {Γ : List CoreTy} {A : CoreTy} (env : CoreVals Γ) (tl : CoreExpr S Γ (.list A)) : Frame S A (.list A)
  | consT {A : CoreTy} (h : CoreVal A) : Frame S (.list A) (.list A)
  | foldL {Γ : List CoreTy} {A B : CoreTy} (env : CoreVals Γ) (init : CoreExpr S Γ B)
      (body : CoreExpr S (A :: B :: Γ) B) : Frame S (.list A) B
  | foldI {Γ : List CoreTy} {A B : CoreTy} (env : CoreVals Γ) (xs : CoreList A)
      (body : CoreExpr S (A :: B :: Γ) B) : Frame S B B
  | fixI {Γ : List CoreTy} {St : CoreTy} (env : CoreVals Γ) (limit : CoreExpr S Γ .i64)
      (stop : CoreExpr S (St :: Γ) .bool) (step : CoreExpr S (St :: Γ) St) : Frame S St (fixTy St)
  | fixL {Γ : List CoreTy} {St : CoreTy} (env : CoreVals Γ) (s : CoreVal St)
      (stop : CoreExpr S (St :: Γ) .bool) (step : CoreExpr S (St :: Γ) St) : Frame S .i64 (fixTy St)
  | fixS {Γ : List CoreTy} {St : CoreTy} (env : CoreVals Γ) (s : CoreVal St) (left count : Int)
      (hb : FixBound left count)
      (stop : CoreExpr S (St :: Γ) .bool) (step : CoreExpr S (St :: Γ) St) : Frame S .bool (fixTy St)
  | fixT {Γ : List CoreTy} {St : CoreTy} (env : CoreVals Γ) (left count : Int) (hb : FixBound left count)
      (stop : CoreExpr S (St :: Γ) .bool) (step : CoreExpr S (St :: Γ) St) : Frame S St (fixTy St)
  | primArgsF {Γ : List CoreTy} {A : CoreTy} (op : PrimOp) (pre post : List CoreTy)
      (heq : (primSig op).ps = pre ++ A :: post) (env : CoreVals Γ) (done : CoreVals pre)
      (rest : Args S Γ post) : Frame S A (primSig op).rt
  | callArgsF {Γ : List CoreTy} {A : CoreTy} (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f)
      (pre post : List CoreTy) (heq : f.params = pre ++ A :: post) (env : CoreVals Γ)
      (done : CoreVals pre) (rest : Args S Γ post) : Frame S A f.result
  | retF {T : CoreTy} : Frame S T T
  | handleF {Γ : List CoreTy} {P T : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P)
      (env : CoreVals Γ) (hd : CoreExpr S (P :: Γ) T) : Frame S T T
  | raiseF {P T : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P) : Frame S P T

inductive Cont (S : Sig) : CoreTy → CoreTy → Type where
  | nil {T : CoreTy} : Cont S T T
  | cons {A B T : CoreTy} (fr : Frame S A B) (k : Cont S B T) : Cont S A T

inductive Control (S : Sig) : CoreTy → Type where
  | evalC {Γ : List CoreTy} {A : CoreTy} (env : CoreVals Γ) (e : CoreExpr S Γ A) : Control S A
  | retC {A : CoreTy} (v : CoreVal A) : Control S A
  | raiseC {A P : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P) (v : CoreVal P) : Control S A

/-- 06 §13: a dependent pair of current result type, control, and typed
    continuation (to the configuration's final type `T`). -/
structure Config (S : Sig) (T : CoreTy) where
  A : CoreTy
  ctl : Control S A
  k : Cont S A T

/-- 06 §14 `SCMFinal T`. -/
inductive Final (S : Sig) (T : CoreTy) where
  | returned (v : CoreVal T)
  | raised {P : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P) (v : CoreVal P)

/-- 06 §15 "c is a final configuration for o": a returning control or a
    raising control at the empty continuation, with that value / residue. -/
def IsFinalConfig {S : Sig} {T : CoreTy} : Config S T → Final S T → Prop
  | ⟨_, .retC v, .nil⟩, o => o = .returned v
  | ⟨_, .raiseC r h v, .nil⟩, o => o = .raised r h v
  | _, _ => False

/-- One transition: a next configuration, a final outcome, or an integrity
    residue (06 §5; never a source outcome). -/
inductive StepResult (S : Sig) (T : CoreTy) where
  | next (c : Config S T)
  | final (o : Final S T)
  | integrity (code : String)

/-! ## §15 One step -/

section Step
variable {S : Sig}

def nxt {T A : CoreTy} (c : Control S A) (k : Cont S A T) : StepResult S T := .next ⟨A, c, k⟩

/-- A primitive / loop residue carries the unit payload; it must be typed
    by the catalog (06 §16 residue-row safety and payload typing). -/
def raiseUnit {B T : CoreTy} (r : RaisedRef) (rest : Cont S B T) : StepResult S T :=
  match h : catalogPt S.catalog r with
  | none => .integrity "[rcic_scm_core_row_safety]"
  | some P => if hp : P = unitTy then nxt (.raiseC r h (hp ▸ unitV)) rest
              else .integrity "[rcic_scm_core_payload]"

def enterI {T : CoreTy} (prog : Bodies S S.fns) (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f)
    (args : CoreVals f.params) (k : Cont S f.result T) : StepResult S T :=
  nxt (.evalC args (prog.at i f hf)) (.cons .retF k)

def fixOutI {St : CoreTy} (c : Bool) (s : CoreVal St) (count : Int) (h : inI64 count) : CoreVal (fixTy St) :=
  .recordV (.cons (.boolV c) (.cons s (.cons (.i64V count h) .nil)))

def pushPrim {Γ : List CoreTy} {T : CoreTy} (op : PrimOp) (env : CoreVals Γ) :
    (ps : List CoreTy) → (primSig op).ps = ps → Args S Γ ps → Cont S (primSig op).rt T → StepResult S T
  | [], _, .nil, _ => .integrity "[rcic_scm_core_stuck]"
  | _ :: post, heq, .cons x rest, k => nxt (.evalC env x) (.cons (.primArgsF op [] post heq env .nil rest) k)

def pushCall {Γ : List CoreTy} {T : CoreTy} (prog : Bodies S S.fns) (i : Nat) (f : FnSig)
    (hf : S.fns.get? i = some f) (env : CoreVals Γ) :
    (ps : List CoreTy) → f.params = ps → Args S Γ ps → Cont S f.result T → StepResult S T
  | [], heq, .nil, k => enterI prog i f hf (heq ▸ .nil) k
  | _ :: post, heq, .cons x rest, k => nxt (.evalC env x) (.cons (.callArgsF i f hf [] post heq env .nil rest) k)

def pushRecord {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) :
    (fs : List (String × CoreTy)) → Fields S Γ fs → Cont S (.record fs) T → StepResult S T
  | [], .nil, k => nxt (A := .record []) (.retC (.recordV .nil)) k
  | (key, _) :: post, .cons _ x rest, k => nxt (.evalC env x) (.cons (.recF _ [] post key rfl env .nil rest) k)

def evalI {Γ : List CoreTy} {T : CoreTy} (prog : Bodies S S.fns) (env : CoreVals Γ) :
    {A : CoreTy} → CoreExpr S Γ A → Cont S A T → StepResult S T
  | _, .lit v, k => nxt (.retC v) k
  | _, .var i h, k => nxt (.retC (env.get i h)) k
  | _, .letE a b, k => nxt (.evalC env a) (.cons (.letF env b) k)
  | _, .ifE c th el, k => nxt (.evalC env c) (.cons (.ifF env th el) k)
  | _, .pairE a b, k => nxt (.evalC env a) (.cons (.pairL env b) k)
  | _, .fstE a, k => nxt (.evalC env a) (.cons .fstF k)
  | _, .sndE a, k => nxt (.evalC env a) (.cons .sndF k)
  | _, .injE _ i h a, k => nxt (.evalC env a) (.cons (.injF i h) k)
  | _, .matchSum s bs _, k => nxt (.evalC env s) (.cons (.matchF env bs) k)
  | _, .recordE xs _, k => pushRecord env _ xs k
  | _, .fieldE i key h r, k => nxt (.evalC env r) (.cons (.fieldF i key h) k)
  | _, .nilE, k => nxt (.retC (.listV .nil)) k
  | _, .consE h tl, k => nxt (.evalC env h) (.cons (.consH env tl) k)
  | _, .foldList l init body, k => nxt (.evalC env l) (.cons (.foldL env init body) k)
  | _, .boundedFix init limit stop step, k => nxt (.evalC env init) (.cons (.fixI env limit stop step) k)
  | _, .prim op args, k => pushPrim op env _ rfl args k
  | _, .call (.local i f hf) args, k => pushCall prog i f hf env _ rfl args k
  | _, .call (.external _ _ _) _, _ => .integrity "[rcic_scm_core_external_call]"
  | _, .raise r h p, k => nxt (.evalC env p) (.cons (.raiseF r h) k)
  | _, .handle r h body hd, k => nxt (.evalC env body) (.cons (.handleF r h env hd) k)

def retI {A T : CoreTy} (prog : Bodies S S.fns) (v : CoreVal A) : Cont S A T → StepResult S T
  | .nil => .final (.returned v)
  | .cons fr rest =>
    match fr, v with
    | .letF env b, v => nxt (.evalC (.cons v env) b) rest
    | .ifF env th el, .boolV c => nxt (.evalC env (if c then th else el)) rest
    | .pairL env b, v => nxt (.evalC env b) (.cons (.pairR v) rest)
    | .pairR a, v => nxt (.retC (.pairV a v)) rest
    | .fstF, .pairV a _ => nxt (.retC a) rest
    | .sndF, .pairV _ b => nxt (.retC b) rest
    | .injF i h, v => nxt (.retC (.injV i _ h v)) rest
    | .matchF env bs, .injV i _ h w => nxt (.evalC (.cons w env) (bs.at i h)) rest
    | .recF fs pre post key heq env done more, v =>
      have hm : (pre ++ [(key, _)]).map Prod.snd = pre.map Prod.snd ++ [_] := List.map_append Prod.snd pre [(key, _)]
      let done' := hm ▸ done.snoc v
      match post, more, heq with
      | [], .nil, heq => nxt (.retC (heq ▸ CoreVal.recordV done')) rest
      | (key2, _) :: post', .cons _ x more', heq =>
          nxt (.evalC env x)
            (.cons (.recF fs (pre ++ [(key, _)]) post' key2
               (heq.trans (List.append_assoc pre [(key, _)] ((key2, _) :: post')).symm) env done' more') rest)
    | .fieldF (fs := fs) i _ h, .recordV xs => nxt (.retC (recordField fs xs i h)) rest
    | .consH env tl, v => nxt (.evalC env tl) (.cons (.consT v) rest)
    | .consT h, .listV xs => nxt (.retC (.listV (.cons h xs))) rest
    | .foldL env init body, .listV xs => nxt (.evalC env init) (.cons (.foldI env xs body) rest)
    | .foldI env xs body, v =>
      match xs with
      | .nil => nxt (.retC v) rest
      | .cons x xs' => nxt (.evalC (.cons x (.cons v env)) body) (.cons (.foldI env xs' body) rest)
    | .fixI env limit stop step, v => nxt (.evalC env limit) (.cons (.fixL env v stop step) rest)
    | .fixL env s stop step, .i64V n hn =>
      if hlt : n < 0 then raiseUnit "negative_loop_bound" rest
      else nxt (.evalC (.cons s env) stop) (.cons (.fixS env s n 0 (fixBound_start hn hlt) stop step) rest)
    | .fixS env s left count hb stop step, .boolV c =>
      if c then nxt (.retC (fixOutI true s count (fixBound_inI64 hb))) rest
      else if hz : left = 0 then nxt (.retC (fixOutI false s count (fixBound_inI64 hb))) rest
      else nxt (.evalC (.cons s env) step) (.cons (.fixT env (left - 1) (count + 1) (fixBound_next hb hz) stop step) rest)
    | .fixT env left count hb stop step, v =>
        nxt (.evalC (.cons v env) stop) (.cons (.fixS env v left count hb stop step) rest)
    | .primArgsF op pre post heq env done more, v =>
      match post, more, heq with
      | [], .nil, heq =>
        match primLaw op (heq ▸ done.snoc v) with
        | .returned w => nxt (.retC w) rest
        | .raised r => raiseUnit r rest
      | _ :: post', .cons x more', heq =>
          nxt (.evalC env x)
            (.cons (.primArgsF op (pre ++ [_]) post'
               (heq.trans (List.append_assoc pre [_] (_ :: post')).symm) env (done.snoc v) more') rest)
    | .callArgsF i f hf pre post heq env done more, v =>
      match post, more, heq with
      | [], .nil, heq => enterI prog i f hf (heq ▸ done.snoc v) rest
      | _ :: post', .cons x more', heq =>
          nxt (.evalC env x)
            (.cons (.callArgsF i f hf (pre ++ [_]) post'
               (heq.trans (List.append_assoc pre [_] (_ :: post')).symm) env (done.snoc v) more') rest)
    | .retF, v => nxt (.retC v) rest
    | .handleF _ _ _ _, v => nxt (.retC v) rest
    | .raiseF r h, v => nxt (.raiseC r h v) rest

def raiseI {A T P : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P) (v : CoreVal P) :
    Cont S A T → StepResult S T
  | .nil => .final (.raised r h v)
  | .cons fr rest =>
    match fr with
    | .handleF (P := P') r' h' env hd =>
      if hr : r' = r then
        have hp : P = P' := Option.some.inj (h.symm.trans (hr ▸ h'))
        nxt (.evalC (.cons (hp ▸ v) env) hd) rest
      else nxt (.raiseC r h v) rest
    | _ => nxt (.raiseC r h v) rest

/-- 06 §15 `scmStep`. -/
def stepI {T : CoreTy} (prog : Bodies S S.fns) (c : Config S T) : StepResult S T :=
  match c with
  | ⟨_, .evalC env e, k⟩ => evalI prog env e k
  | ⟨_, .retC v, k⟩ => retI prog v k
  | ⟨_, .raiseC r h v, k⟩ => raiseI r h v k

/-- 06 §15: `SCMStep(c, c') ↔ scmStep(c) = next c'`. -/
def SCMStep {T : CoreTy} (prog : Bodies S S.fns) (c c' : Config S T) : Prop :=
  ∃ h : stepI prog c = .next c', True

/-- 06 §15 `SCMRuns n c c'`: exactly `n` transitions. -/
inductive SCMRuns {T : CoreTy} (prog : Bodies S S.fns) : Nat → Config S T → Config S T → Prop where
  | refl (c : Config S T) : SCMRuns prog 0 c c
  | step {n : Nat} {c c' c'' : Config S T} : stepI prog c = .next c' → SCMRuns prog n c' c'' →
      SCMRuns prog (n + 1) c c''

/-- Concatenation of `SCMRuns` witnesses (06 §15): `m` transitions then `n`
transitions is `m + n` transitions. Shared below every `stepI`-level
refinement module (`RcicLevelEqnArm`, `RcicScmStepRefines` / #7116). -/
theorem SCMRuns.trans {S : Sig} {T : CoreTy} {prog : Bodies S S.fns}
    {m n : Nat} {c1 c2 c3 : Config S T}
    (h1 : SCMRuns prog m c1 c2) (h2 : SCMRuns prog n c2 c3) :
    SCMRuns prog (m + n) c1 c3 := by
  induction h1 with
  | refl => rw [Nat.zero_add]; exact h2
  | step hs _ ih => rw [Nat.succ_add]; exact SCMRuns.step hs (ih h2)

/-- 06 §14 `SCMRunResult T`, with the integrity residue kept apart. -/
inductive RunI (S : Sig) (T : CoreTy) where
  | done (o : Final S T) (steps : Int)
  | suspended (c : Config S T) (steps : Int)
  | integrity (code : String)

/-- The runner: finality before budget; one unit per transition. -/
def runLoopI {T : CoreTy} (prog : Bodies S S.fns) : Config S T → Nat → Int → RunI S T
  | c, 0, steps =>
    match stepI prog c with
    | .integrity code => .integrity code
    | .final o => .done o steps
    | .next _ => .suspended c steps
  | c, l + 1, steps =>
    match stepI prog c with
    | .integrity code => .integrity code
    | .final o => .done o steps
    | .next c' => runLoopI prog c' l (steps + 1)

end Step

/-! ## Erasure intrinsic → raw (the carrier's first-order records) -/

def primName : PrimOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .neg => "neg" | .div => "div" | .mod => "mod"
  | .lt => "lt" | .eq => "eq" | .strLen => "str_len" | .strSlice => "str_slice"
  | .strSplit => "str_split" | .strToI64 => "str_to_i64" | .bytesPack => "bytes_pack"
  | .bytesLen => "bytes_len"

section Erase
variable {S : Sig}

mutual
def CoreExpr.erase : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → RawExpr
  | _, _, .lit (T := T) v => .lit v.erase T
  | _, _, .var i _ => .var i
  | _, _, .letE a b => .letE a.erase b.erase
  | _, _, .ifE c th el => .ifE c.erase th.erase el.erase
  | _, _, .pairE a b => .pair a.erase b.erase
  | _, _, .fstE a => .fst a.erase
  | _, _, .sndE a => .snd a.erase
  | _, _, .injE ts i _ a => .inj i ts a.erase
  | _, _, .matchSum s bs _ => .matchE s.erase bs.erase
  | _, _, .recordE (fs := fs) xs _ => .recordE (fs.map Prod.fst) xs.erase
  | _, _, .fieldE i _ _ r => .field r.erase i
  | _, _, .nilE (A := A) => .nil A
  | _, _, .consE h tl => .cons h.erase tl.erase
  | _, _, .foldList l init body => .fold l.erase init.erase body.erase
  | _, _, .boundedFix init limit stop step => .fix init.erase limit.erase stop.erase step.erase
  | _, _, .prim op args => .prim (primName op) args.erase
  | _, _, .call (.local i _ _) args => .call (.local i) args.erase
  | _, _, .call (.external r _ _) args => .call (.ext r) args.erase
  | _, _, .raise (T := T) r _ p => .raise r p.erase T
  | _, _, .handle r _ body hd => .handle r body.erase hd.erase
def Branches.erase : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → List RawExpr
  | _, _, _, .nil => []
  | _, _, _, .cons b bs => b.erase :: bs.erase
def Fields.erase : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → List RawExpr
  | _, _, .nil => []
  | _, _, .cons _ x xs => x.erase :: xs.erase
def Args.erase : {Γ ps : List CoreTy} → Args S Γ ps → List RawExpr
  | _, _, .nil => []
  | _, _, .cons x xs => x.erase :: xs.erase
end

def Frame.erase {A B : CoreTy} : Frame S A B → Raw.Frame
  | .letF env b => .letF env.erase b.erase
  | .ifF env th el => .ifF env.erase th.erase el.erase
  | .pairL env b => .pairL env.erase b.erase
  | .pairR a => .pairR a.erase
  | .fstF => .fstF
  | .sndF => .sndF
  | .injF i _ => .injF i
  | .matchF env bs => .matchF env.erase bs.erase
  | .recF _ _ _ _ _ env done rest => .recF env.erase done.erase rest.erase
  | .fieldF i _ _ => .fieldF i
  | .consH env tl => .consH env.erase tl.erase
  | .consT h => .consT h.erase
  | .foldL env init body => .foldL env.erase init.erase body.erase
  | .foldI env xs body => .foldI env.erase xs.erase body.erase
  | .fixI env limit stop step => .fixI env.erase limit.erase stop.erase step.erase
  | .fixL env s stop step => .fixL env.erase s.erase stop.erase step.erase
  | .fixS env s left count _ stop step => .fixS env.erase s.erase left count stop.erase step.erase
  | .fixT env left count _ stop step => .fixT env.erase left count stop.erase step.erase
  | .primArgsF op _ _ _ env done rest => .argsF env.erase 0 (primName op) 0 done.erase rest.erase
  | .callArgsF i _ _ _ _ _ env done rest => .argsF env.erase 1 "" i done.erase rest.erase
  | .retF => .retF
  | .handleF r _ env hd => .handleF r env.erase hd.erase
  | .raiseF r _ => .raiseF r

def Cont.erase {A T : CoreTy} : Cont S A T → List Raw.Frame
  | .nil => []
  | .cons fr k => fr.erase :: k.erase

def Control.erase {A : CoreTy} : Control S A → Raw.Ctl
  | .evalC env e => .evalC env.erase e.erase
  | .retC v => .retC v.erase
  | .raiseC r _ v => .raiseC r v.erase

def Config.erase {T : CoreTy} (c : Config S T) : Raw.Config := ⟨c.ctl.erase, c.k.erase⟩

def RunI.toOut {T : CoreTy} : RunI S T → Raw.Out
  | .done (.returned v) steps => Raw.runRes 1 ⟨.retC v.erase, []⟩ v.erase "" steps
  | .done (.raised r _ v) steps => Raw.runRes 2 ⟨.raiseC r v.erase, []⟩ v.erase r steps
  | .suspended c steps => Raw.runRes 3 c.erase unitRaw "" steps
  | .integrity code => Raw.refuse code

end Erase

/-! ## The entry run on intrinsic configurations (form 2 of the carrier) -/

def entryI (fuel : Int) (p : RawProg) (args : List Val) (n : Int) : Raw.Out :=
  match progCheck fuel p with
  | .error c => Raw.refuse c
  | .ok ⟨bodies, _⟩ =>
    if he : p.entry < 0 then Raw.refuse "[rcic_scm_typing_entry]" else
    match hf : (sigOf p).fns.get? p.entry.toNat with
    | none => Raw.refuse "[rcic_scm_typing_entry]"
    | some f =>
      match toCoreVals f.params args with
      | none => Raw.refuse "[rcic_scm_core_ill_typed_args]"
      | some env =>
        if n < 0 then Raw.refuse "[rcic_scm_core_budget]"
        else if n > 4096 then Raw.refuse "[rcic_scm_core_bound]"
        else
          let c0 : Config (sigOf p) f.result := ⟨f.result, .evalC env (bodies.at p.entry.toNat f hf), .nil⟩
          (runLoopI bodies c0 n.toNat 0).toOut

end Rcic.Scm
