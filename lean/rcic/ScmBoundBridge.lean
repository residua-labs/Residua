/-
M4 stage A — 06 §19 intrinsic↔wire bridge: the typed→wire encoder half
(06:404–419).

§19's directions split into two halves. This module lands the half that
needs no carrier acceptance and no wire inverse:

* the typed→wire encoders `ctlOf`/`frmOf`/`contOf`/`cfgOf`/`finOf`, the
  first constructive half of `config_at : Config c ∧ ProgramAt → ConfigAt`
  (06:412): they produce the `Tagged`/`CfgO`/`FinO` objects whose
  `cfgSchema`/`finSchema` encodings are the canonical bytes;
* the raw-erasure roundtrips `ctlToRaw (ctlOf c) = c.erase`,
  `frmToRaw (frmOf f) = f.erase`, `cfgToRaw (cfgOf c) = c.erase`,
  `finToRaw (finOf o) = finalErase o` — 06:417's `→` direction at the raw
  layer (the wire object decodes to the same raw configuration the typed
  object erases to);
* the kind-24 member `runResultRel` intro lemmas (`…_done`, `…_suspended`)
  plus their refusal teeth (`…_refused`) — the member is the endpoint's
  outcome at tag 0 and its raw configuration at tag 1, never the other;
* the value bridge's wire→intrinsic direction (06:410, `:404`): a
  `ValueAt` byte string decodes to a unique `Val`, and that `Val` to a
  unique `CoreVal` at the bound type (`valueAt_dec_uniq`,
  `valueAt_coreVal_uniq`);
* the wire→intrinsic projections `step_of_scmStepAt` /
  `runs_of_scmRunsAt` / `runs_of_entryRunsAt` — the §19 `←` directions
  already carried by M3's ∃-typed witnesses.

Still open (stage B, the carrier-acceptance half): `valueAt_of_enc`
(06:409 — needs `coreTypeSchema`/`dec0` inverses), `programAt_of_progCheck`
(06:411 — needs `objEnc`/`objDec` inverses and `bpBuild` acceptance),
`configAt_of_wf` (06:412 — needs `cfgTy`/`frameOk` acceptance of `frmOf`
objects and the typed→`elabE` completeness lemma), `outcome_at` (06:413),
`scmStepAt_of_step`/`scmRunsAt_of_runs` (06:414/415 — need `ConfigAt` of
the encoded endpoints), and the entry-init/final-outcome correspondence
(06:418/419). `SCMLogicalEmbeddingClosed` stays partial; no closure claim
moves.
-/

import rcic.ScmBoundExec
import rcic.ScmElabComplete
import rcic.ScmErase
import rcic.ScmWireInv

namespace Rcic.Scm.BoundBridge

open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.CfgAt Rcic.Scm.CfgWire Rcic.BoundObject
open Rcic.Scm.BoundCfg Rcic.Scm.BoundProgAt Rcic.Scm.BoundExec Rcic.Scm.BoundTV
open Rcic.Scm.RawRel Rcic.Scm.ElabComplete

variable {S : Sig}

/-! ## Item codecs on encoder output -/

def tyItem (ts : List CoreTy) : Item := .list (ts.map .ty)
def valItem (vs : List Val) : Item := .list (vs.map .val)
def exItem (es : List RawExpr) : Item := .list (es.map .expr)

@[simp] theorem asTy_ty (t : CoreTy) : asTy (.ty t) = t := rfl
@[simp] theorem asVal_val (v : Val) : asVal (.val v) = v := rfl
@[simp] theorem asExpr_expr (e : RawExpr) : asExpr (.expr e) = e := rfl
@[simp] theorem asNum_num (n : Int) : asNum (.num n) = n := rfl
@[simp] theorem asStr_str (s : String) : asStr (.str s) = s := rfl

@[simp] theorem itm_zero (x : Item) (xs : List Item) : itm (x :: xs) 0 = x := rfl
@[simp] theorem itm_succ (x : Item) (xs : List Item) (n : Nat) :
    itm (x :: xs) (n + 1) = itm xs n := rfl

@[simp] theorem valL_valItem (vs : List Val) : valL (valItem vs) = vs := by
  simp only [valItem, valL, asList]
  induction vs <;> simp_all

@[simp] theorem tyL_tyItem (ts : List CoreTy) : tyL (tyItem ts) = ts := by
  simp only [tyItem, tyL, asList]
  induction ts <;> simp_all

@[simp] theorem exL_exItem (es : List RawExpr) : exL (exItem es) = es := by
  simp only [exItem, exL, asList]
  induction es <;> simp_all

/-! ## Typed→wire encoders -/

/-- The typed control as a wire `Tagged` (06 §13's control layouts). -/
def ctlOf {A : CoreTy} : Control S A → Tagged
  | @Control.evalC _ Γ _ env e =>
      ⟨0, [tyItem Γ, valItem env.erase, .expr e.erase]⟩
  | .retC v => ⟨1, [.ty A, .val v.erase]⟩
  | .raiseC r _ v => ⟨2, [.ty A, .str r, .val v.erase]⟩

/-- The typed frame as a wire `Tagged`, tags 0–21 in `frameKinds` order;
    the two leading items are the frame's input and output types (tag 13
    carries the folded element type in between), the rest the erased
    payload in the schema's order. -/
def frmOf {A B : CoreTy} : Frame S A B → Tagged
  | @Frame.letF _ Γ _ _ env b =>
      ⟨0, [.ty A, .ty B, tyItem Γ, valItem env.erase, .expr b.erase]⟩
  | @Frame.ifF _ Γ _ env th el =>
      ⟨1, [.ty A, .ty B, tyItem Γ, valItem env.erase, .expr th.erase,
           .expr el.erase]⟩
  | @Frame.pairL _ Γ _ _ env b =>
      ⟨2, [.ty A, .ty B, tyItem Γ, valItem env.erase, .expr b.erase]⟩
  | .pairR a => ⟨3, [.ty A, .ty B, .val a.erase]⟩
  | .fstF => ⟨4, [.ty A, .ty B]⟩
  | .sndF => ⟨5, [.ty A, .ty B]⟩
  | .injF i _ => ⟨6, [.ty A, .ty B, .num i]⟩
  | @Frame.matchF _ Γ _ _ env bs =>
      ⟨7, [.ty A, .ty B, tyItem Γ, valItem env.erase, exItem bs.erase]⟩
  | @Frame.recF _ Γ _ _ _ _ _ _ env done rest =>
      ⟨8, [.ty A, .ty B, tyItem Γ, valItem env.erase,
           valItem done.erase, exItem rest.erase]⟩
  | .fieldF i _ _ => ⟨9, [.ty A, .ty B, .num i]⟩
  | @Frame.consH _ Γ _ env tl =>
      ⟨10, [.ty A, .ty B, tyItem Γ, valItem env.erase, .expr tl.erase]⟩
  | .consT h => ⟨11, [.ty A, .ty B, .val h.erase]⟩
  | @Frame.foldL _ Γ _ _ env init body =>
      ⟨12, [.ty A, .ty B, tyItem Γ, valItem env.erase,
            .expr init.erase, .expr body.erase]⟩
  | @Frame.foldI _ Γ A' _ env xs body =>
      ⟨13, [.ty A, .ty B, .ty A', tyItem Γ, valItem env.erase,
            valItem xs.erase, .expr body.erase]⟩
  | @Frame.fixI _ Γ _ env limit stop step =>
      ⟨14, [.ty A, .ty B, tyItem Γ, valItem env.erase,
            .expr limit.erase, .expr stop.erase, .expr step.erase]⟩
  | @Frame.fixL _ Γ _ env s stop step =>
      ⟨15, [.ty A, .ty B, tyItem Γ, valItem env.erase, .val s.erase,
            .expr stop.erase, .expr step.erase]⟩
  | @Frame.fixS _ Γ _ env s left count _ stop step =>
      ⟨16, [.ty A, .ty B, tyItem Γ, valItem env.erase, .val s.erase,
            .num left, .num count, .expr stop.erase, .expr step.erase]⟩
  | @Frame.fixT _ Γ _ env left count _ stop step =>
      ⟨17, [.ty A, .ty B, tyItem Γ, valItem env.erase, .num left,
            .num count, .expr stop.erase, .expr step.erase]⟩
  | @Frame.primArgsF _ Γ _ op _ _ _ env done rest =>
      ⟨18, [.ty A, .ty B, tyItem Γ, valItem env.erase, .num 0,
            .str (primName op), .num 0, valItem done.erase, exItem rest.erase]⟩
  | @Frame.callArgsF _ Γ _ i _ _ _ _ _ env done rest =>
      ⟨18, [.ty A, .ty B, tyItem Γ, valItem env.erase, .num 1, .str "",
            .num i, valItem done.erase, exItem rest.erase]⟩
  | .retF => ⟨19, [.ty A, .ty B]⟩
  | @Frame.handleF _ Γ _ _ r _ env hd =>
      ⟨20, [.ty A, .ty B, .str r, tyItem Γ, valItem env.erase, .expr hd.erase]⟩
  | .raiseF r _ => ⟨21, [.ty A, .ty B, .str r]⟩

/-- The typed continuation as the wire frame list. -/
def contOf {A T : CoreTy} : Cont S A T → List Tagged
  | .nil => []
  | .cons fr k => frmOf fr :: contOf k

/-- The typed configuration as a wire `CfgO`: the stored result type, the
    encoded control, the encoded frame chain. -/
def cfgOf {T : CoreTy} (c : Config S T) : CfgO := ⟨T, ctlOf c.ctl, contOf c.k⟩

/-- The typed final outcome as a wire `FinO` (kind-23 layouts: tag 0 a
    returned value, tag 1 a raised residue and payload). -/
def finOf {T : CoreTy} : Final S T → FinO
  | .returned v => ⟨T, 0, [.val v.erase]⟩
  | .raised r _ v => ⟨T, 1, [.str r, .val v.erase]⟩

/-- The run member of a `RunI` under `runResultRel`'s shape: done runs
    carry the `FinO`, suspended runs the `CfgO` (integrity refusals carry
    no bound member). -/
def runMemberOf {T : CoreTy} : RunI S T → Option (Int × CX)
  | .done o _ => some (0, .fin (finOf o))
  | .suspended c _ => some (1, .cfg (cfgOf c))
  | .integrity _ => none

/-! ## Raw-erasure roundtrips (06:417 `→` at the raw layer) -/

theorem ctlToRaw_ctlOf {A : CoreTy} (c : Control S A) :
    ctlToRaw (ctlOf c) = c.erase := by
  cases c <;> simp [ctlOf, ctlToRaw, Control.erase]

theorem frmToRaw_frmOf {A B : CoreTy} (f : Frame S A B) :
    frmToRaw (frmOf f) = f.erase := by
  cases f <;> simp [frmOf, frmToRaw, Frame.erase]

theorem contOf_map_frmToRaw {A T : CoreTy} (k : Cont S A T) :
    (contOf k).map frmToRaw = k.erase := by
  induction k with
  | nil => rfl
  | cons fr k ih => simp [contOf, frmToRaw_frmOf, Cont.erase, ih]

theorem cfgToRaw_cfgOf {T : CoreTy} (c : Config S T) :
    cfgToRaw (cfgOf c) = c.erase := by
  cases c; simp [cfgOf, cfgToRaw, ctlToRaw_ctlOf, contOf_map_frmToRaw, Config.erase]

theorem finToRaw_finOf {T : CoreTy} (o : Final S T) :
    finToRaw (finOf o) = finalErase o := by
  cases o <;> rfl

theorem runToRaw_runMemberOf_done {T : CoreTy} (o : Final S T) :
    runToRaw 0 (.fin (finOf o)) =
      some (.done (finalErase o).1 (finalErase o).2.1 (finalErase o).2.2) := by
  cases o <;> rfl

theorem runToRaw_runMemberOf_suspended {T : CoreTy} (c : Config S T) :
    runToRaw 1 (.cfg (cfgOf c)) = some (.suspended c.erase) := by
  unfold runToRaw
  simp [cfgToRaw_cfgOf]

/-! ## Carrier value checks on erased typed values -/

/-- A `CoreVal`'s erasure passes the carrier's `valOk` at its own type —
    `erase_toCore` supplies the `toCore` round trip. -/
theorem valOk_of_coreVal {T : CoreTy} (v : CoreVal T) : valOk v.erase T = true := by
  simp [valOk, Erase.erase_toCore]

/-- A `CoreVals` environment's erasure passes `valsOk` at its type list. -/
theorem valsOk_of_coreVals : ∀ {Γ : List CoreTy} (env : CoreVals Γ),
    valsOk env.erase Γ = true
  | _, .nil => rfl
  | _, .cons x xs => by
      have ih := valsOk_of_coreVals xs
      simp only [CoreVals.erase, valsOk, List.length_cons, List.zip_cons_cons,
        List.all_cons, Bool.and_eq_true, beq_iff_eq] at ih ⊢
      exact ⟨congrArg (· + 1) ih.1, valOk_of_coreVal x, ih.2⟩

/-! ## Kind-24 member relation: intro lemmas and their teeth -/

/-- `IsFinalConfig` is deterministic in the outcome: a final
    configuration carries exactly one outcome shape. -/
theorem isFinalConfig_deterministic {T : CoreTy} {c : Config S T} {o o' : Final S T}
    (h : IsFinalConfig c o) (h' : IsFinalConfig c o') : o = o' := by
  obtain ⟨A, ctl, k⟩ := c
  cases ctl <;> cases k <;> simp_all [IsFinalConfig]

/-- 06:414/415's member half for done runs: the kind-24 member of a
    finished `SCMRuns` endpoint is its `Final` outcome, `finalErase`d. -/
theorem runResultRel_of_done {T : CoreTy} (c' : Config S T) (o : Final S T)
    (hf : IsFinalConfig c' o) :
    runResultRel c' 0 (.fin (finOf o)) := by
  unfold runResultRel
  rw [runToRaw_runMemberOf_done]
  exact ⟨o, hf, rfl⟩

/-- The suspended member is the endpoint's raw configuration. -/
theorem runResultRel_of_suspended {T : CoreTy} (c' : Config S T) :
    runResultRel c' 1 (.cfg (cfgOf c')) := by
  unfold runResultRel
  rw [runToRaw_runMemberOf_suspended]

/-- Tooth: a `.cfg` member is never the member of a tag-0 (done) run —
    `runToRaw` refuses the shape, so the relation is empty. -/
theorem runResultRel_done_cfg_refused {T : CoreTy} (c' : Config S T) (co : CfgO) :
    ¬ runResultRel c' 0 (.cfg co) := by
  unfold runResultRel; simp [runToRaw]

/-- Tooth: a `.fin` member is never the member of a tag-1 (suspended) run. -/
theorem runResultRel_suspended_fin_refused {T : CoreTy} (c' : Config S T) (f : FinO) :
    ¬ runResultRel c' 1 (.fin f) := by
  unfold runResultRel; simp [runToRaw]

/-- Tooth: a done member whose decoded triple is not `c'`'s outcome is
    refused — the `finalErase` equality is load-bearing. -/
theorem runResultRel_done_wrong_outcome_refused {T : CoreTy} (c' : Config S T)
    (o : Final S T) (w : FinO)
    (hf : IsFinalConfig c' o) (hw : finToRaw w ≠ finalErase o) :
    ¬ runResultRel c' 0 (.fin w) := by
  intro h
  unfold runResultRel at h
  simp only [runToRaw] at h
  obtain ⟨o', hfo', heq⟩ := h
  have hd := isFinalConfig_deterministic hf hfo'
  rw [← hd] at heq
  exact hw (by rw [heq])

/-! ## Value bridge: the wire→intrinsic direction (06:404, :410) -/

/-- `T.ty` is what the schema decode of `T`'s type bytes returns. -/
theorem boundCoreType_ty {T : BoundCoreType} {t : CoreTy}
    (h : coreTypeSchema.decode T.type_bytes = some t) : T.ty = t := by
  simp [BoundCoreType.ty, h]

/-- 06:410 `←`: a `ValueAt` byte string names a unique decoded `Val` —
    `valueBytesAt` is functional. -/
theorem valueAt_dec_uniq (T : BoundCoreType) (vb : String) (h : ValueAt T vb) :
    ∃ v : Val, valueBytesAt vb = some v ∧
      ∀ w : Val, valueBytesAt vb = some w → w = v := by
  obtain ⟨_, _, v, hv, _⟩ := h
  exact ⟨v, hv, fun w hw => (Option.some.inj (hv.symm.trans hw)).symm⟩

/-- The intrinsic decoded value is unique: the `CoreVal` at `T.ty` whose
    `toCore` preimage is the decoded `Val` is determined. -/
theorem valueAt_coreVal_uniq (T : BoundCoreType) (vb : String) (h : ValueAt T vb) :
    ∃ cv : CoreVal T.ty, (∃ v : Val, valueBytesAt vb = some v ∧
      toCore T.ty v = some cv) ∧
      ∀ cv' : CoreVal T.ty, (∃ v : Val, valueBytesAt vb = some v ∧
        toCore T.ty v = some cv') → cv' = cv := by
  obtain ⟨t, hd, v, hv, hok⟩ := h
  rw [boundCoreType_ty hd]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp hok
  refine ⟨cv, ⟨v, hv, hcv⟩, ?_⟩
  intro cv' ⟨v', hv', hcv'⟩
  have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
  subst hvv
  exact (Option.some.inj (hcv.symm.trans hcv')).symm

/-- The `valueBytesAt` roundtrip on canonical bytes, shared by
    `valueAt_of_enc` and the SCM-014 completeness consumers: under the wire
    bound `dqV` and the decoder gas/fuel budgets at the input's own length,
    `encVal v` decodes back to exactly `v`. -/
theorem valueBytesAt_encVal (v : Val)
    (hdq : dqV v)
    (hg : valGas v ≤ gasFor (↑(encVal v).length) (encVal v).length - 1)
    (hf : (valFuel v : Int) ≤ (encVal v).length) :
    valueBytesAt (encVal v) = some v := by
  unfold valueBytesAt dec0
  dsimp only
  rw [show ((encVal v).toList.toArray).size = (encVal v).length from
        by simp only [Array.size_toArray]; rfl]
  rw [show gasFor (↑(encVal v).length) (encVal v).length =
        (gasFor (↑(encVal v).length) (encVal v).length - 1) + 1 from by
        unfold gasFor; omega]
  rw [dec_one ((encVal v).toList.toArray) _ _ 0 _ (.val v)
        (decVal_enc v ((encVal v).toList.toArray) _
          (↑(encVal v).length) 0 [] (by simp) hg hf hdq)
        (by omega : ¬ (↑(encVal v).length : Int) < 0)]
  dsimp only
  rw [if_pos ⟨by rw [Nat.zero_add]; rfl, rfl⟩]
  rfl

/-- 06:409 `→` (M4 stage-B, the carrier-acceptance half): a `Val` that
    elaborates at `T.ty` encodes to canonical value bytes —
    `ValueAt T (encVal v)`. `hdq`/`hg`/`hf` are the wire-bound
    scope-out the carrier's acceptance requires: `dqV` well-formedness,
    plus decoder gas/fuel budgets at the input's own length (the
    `coreTypeSchema.decode` convention). -/
theorem valueAt_of_enc (T : BoundCoreType) (v : Val)
    (hdq : dqV v)
    (hg : valGas v ≤ gasFor (↑(encVal v).length) (encVal v).length - 1)
    (hf : (valFuel v : Int) ≤ (encVal v).length)
    (hty : (toCore T.ty v).isSome = true) :
    ValueAt T (encVal v) := by
  have hT := T.type_at
  unfold CanonicalCoreTypeAt CanonicalObjectAt at hT
  obtain ⟨hdec, hdig, hex⟩ := hT
  cases hd : coreTypeSchema.decode T.type_bytes with
  | none => rw [hd] at hdec; exact hdec.elim
  | some t =>
    exact ⟨t, hd, v, valueBytesAt_encVal v hdq hg hf,
      by rw [boundCoreType_ty hd] at hty; exact hty⟩

/-! ## Wire→intrinsic projections (06 §19 `←`) -/

/-- 06:414 `←`: `SCMStepAt` supplies an intrinsic `SCMStep` between
    configurations whose erasures are the decoded wire endpoints. -/
theorem step_of_scmStepAt {profile : String} {P : BoundCoreProgram profile}
    {ri ro : Ref} {bi bo : String} (h : SCMStepAt P ri bi ro bo) :
    ∃ T : CoreTy, ∃ c c' : Config (sigOf P.prog) T,
      ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
        ∃ F : Int, progCheck F P.prog = .ok out ∧ SCMStep out.1 c c' ∧
          ∃ ci co : CfgO, cfgSchema.decode bi = some ci ∧ cfgToRaw ci = c.erase ∧
            cfgSchema.decode bo = some co ∧ cfgToRaw co = c'.erase := by
  obtain ⟨T, c, c', out, F, ci, co, hpc, _, hci, hce, _, hco, hce', hst⟩ := h
  exact ⟨T, c, c', out, F, hpc, hst, ci, co, hci, hce, hco, hce'⟩

/-- 06:415 `←`: `SCMRunsAt` supplies an intrinsic `SCMRuns` plus the
    kind-24 member's outcome/configuration correspondence. -/
theorem runs_of_scmRunsAt {profile : String} {P : BoundCoreProgram profile}
    {n : Nat} {ri rr : Ref} {bi br : String} (h : SCMRunsAt P n ri bi rr br) :
    ∃ T : CoreTy, ∃ c c' : Config (sigOf P.prog) T,
      ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
        ∃ F : Int, progCheck F P.prog = .ok out ∧ SCMRuns out.1 n c c' ∧
          ∃ ci : CfgO, ∃ tag : Int, ∃ m : CX,
            cfgSchema.decode bi = some ci ∧ cfgToRaw ci = c.erase ∧
            runSchema.decode br = some (tag, m) ∧ runResultRel c' tag m := by
  obtain ⟨T, c, c', out, F, ci, tag, m, hpc, _, hci, hce, _, hrd, hrel, hrs⟩ := h
  exact ⟨T, c, c', out, F, hpc, hrs, ci, tag, m, hci, hce, hrd, hrel⟩

/-- 06:418/419 `←`: `EntryRunsAt` supplies an `SCMRuns` from the typed
    entry initialization to the member's endpoint. -/
theorem runs_of_entryRunsAt {profile : String} {P : BoundCoreProgram profile}
    {argBytes : List String} {n : Nat} {rr : Ref} {br : String}
    (h : EntryRunsAt P argBytes n rr br) :
    ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
      ∃ F : Int, ∃ ef : FnSig,
      ∃ hf : (sigOf P.prog).fns.get? P.prog.entry.toNat = some ef,
      ∃ env : CoreVals ef.params, ∃ c' : Config (sigOf P.prog) ef.result,
      ∃ tag : Int, ∃ m : CX,
        progCheck F P.prog = .ok out ∧
        runSchema.decode br = some (tag, m) ∧ runResultRel c' tag m ∧
        SCMRuns out.1 n ⟨ef.result, .evalC env (out.1.at P.prog.entry.toNat ef hf), .nil⟩ c' := by
  obtain ⟨out, F, ef, hf, env, c', tag, m, hpc, _, _, hrd, hrel, hrs⟩ := h
  exact ⟨out, F, ef, hf, env, c', tag, m, hpc, hrd, hrel, hrs⟩

/-! ## Carrier acceptance on encoder output (06 §19 `→`, stage B)

`cfgTy`/`finOk` fuel is `fuelN fuel`, so the premise every lemma carries
is an `exprFuel` bound on the erased expressions the object stores:
`frExprs`/`ctlExprs`/`contExprs` collect them in `frmOf`/`ctlOf`/`contOf`
payload order. -/

/-- The erased expressions inside a typed frame, in `frmOf` payload
    order (the fuel premise for `frameOk` acceptance). -/
def frExprs {A B : CoreTy} : Frame S A B → List RawExpr
  | .letF _ b => [b.erase]
  | .ifF _ th el => [th.erase, el.erase]
  | .pairL _ b => [b.erase]
  | .pairR _ => []
  | .fstF => []
  | .sndF => []
  | .injF _ _ => []
  | .matchF _ bs => bs.erase
  | .recF _ _ _ _ _ _ _ rest => rest.erase
  | .fieldF _ _ _ => []
  | .consH _ tl => [tl.erase]
  | .consT _ => []
  | .foldL _ i b => [i.erase, b.erase]
  | .foldI _ _ b => [b.erase]
  | .fixI _ l s st => [l.erase, s.erase, st.erase]
  | .fixL _ _ s st => [s.erase, st.erase]
  | .fixS _ _ _ _ _ s st => [s.erase, st.erase]
  | .fixT _ _ _ _ s st => [s.erase, st.erase]
  | .primArgsF _ _ _ _ _ _ rest => rest.erase
  | .callArgsF _ _ _ _ _ _ _ _ rest => rest.erase
  | .retF => []
  | .handleF _ _ _ hd => [hd.erase]
  | .raiseF _ _ => []

/-- The erased expression inside a typed control (the `evalC` body). -/
def ctlExprs {A : CoreTy} : Control S A → List RawExpr
  | .evalC _ e => [e.erase]
  | .retC _ => []
  | .raiseC _ _ _ => []

/-- The erased expressions inside a typed continuation. -/
def contExprs {A T : CoreTy} : Cont S A T → List RawExpr
  | .nil => []
  | .cons fr k => frExprs fr ++ contExprs k

/-- `CoreVals.erase` preserves the type-list length. -/
theorem CoreVals_erase_length : ∀ {Γ : List CoreTy} (env : CoreVals Γ),
    env.erase.length = Γ.length
  | _, .nil => rfl
  | _, .cons _ xs => congrArg Nat.succ (CoreVals_erase_length xs)

/-- A `CoreList`'s erased elements all pass `valOk` at the element type. -/
theorem coreList_all_valOk {t : CoreTy} : ∀ (xs : CoreList t),
    (xs.erase).all (fun v => valOk v t) = true
  | .nil => rfl
  | .cons x xs => by
      simp only [CoreList.erase, List.all_cons, Bool.and_eq_true]
      exact ⟨valOk_of_coreVal x, coreList_all_valOk xs⟩

/-- The fix record's state slot decodes to the state type. -/
theorem fixState_fixTy (st : CoreTy) : fixState (fixTy st) = some st := rfl

/-- `exprsOk` accepts an `Args` spine's erasure at its own type list. -/
theorem exprsOk_of_Args {p : RawProg} {Γ : List CoreTy} : ∀ {ps : List CoreTy}
    (as : Args (sigOf p) Γ ps) (fuel : Int)
    (hf : ∀ e ∈ as.erase, (exprFuel e : Int) ≤ fuel),
    exprsOk fuel p Γ as.erase ps = true
  | _, .nil, _, _ => rfl
  | _, .cons x xs, fuel, hf => by
      have ih := exprsOk_of_Args xs fuel
        (fun e he => hf _ (List.mem_cons_of_mem _ he))
      unfold exprsOk at ih ⊢
      rw [Args_erase_length] at ih
      simp only [Args.erase, List.length_cons, Args_erase_length,
        beq_self_eq_true, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, Bool.true_and] at ih ⊢
      exact ⟨hasTy_of_coreExpr x fuel (hf _ (List.mem_cons_self _ _)), ih⟩

/-- `exprsOk` accepts a `Fields` spine's erasure at the field types. -/
theorem exprsOk_of_Fields {p : RawProg} {Γ : List CoreTy} :
    ∀ {fs : List (String × CoreTy)}
    (xs : Fields (sigOf p) Γ fs) (fuel : Int)
    (hf : ∀ e ∈ xs.erase, (exprFuel e : Int) ≤ fuel),
    exprsOk fuel p Γ xs.erase (fs.map Prod.snd) = true
  | _, .nil, _, _ => rfl
  | _, .cons _ x xs, fuel, hf => by
      have ih := exprsOk_of_Fields xs fuel
        (fun e he => hf _ (List.mem_cons_of_mem _ he))
      unfold exprsOk at ih ⊢
      rw [Fields_erase_length, List.length_map] at ih
      simp only [Fields.erase, List.length_cons, List.map_cons,
        Fields_erase_length, List.length_map, beq_self_eq_true,
        List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        Bool.true_and] at ih ⊢
      exact ⟨hasTy_of_coreExpr x fuel (hf _ (List.mem_cons_self _ _)), ih⟩

/-- The `matchF` branch check accepts a `Branches` spine's erasure:
    every erased branch types at its own sum arm. -/
theorem branches_all_of_Branches {p : RawProg} {Γ : List CoreTy} :
    ∀ {ts : List CoreTy} {T : CoreTy}
    (bs : Branches (sigOf p) Γ ts T) (fuel : Int)
    (hf : ∀ e ∈ bs.erase, (exprFuel e : Int) ≤ fuel),
    (bs.erase.zip ts).all (fun (b, t) => hasTy fuel p (t :: Γ) b T) = true
  | _, _, .nil, _, _ => rfl
  | _, _, .cons b bs, fuel, hf => by
      simp only [Branches.erase, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true]
      exact ⟨hasTy_of_coreExpr b fuel (hf _ (List.mem_cons_self _ _)),
             branches_all_of_Branches bs fuel
               (fun e he => hf _ (List.mem_cons_of_mem _ he))⟩

/-- Every `frmOf` frame carries its input and output types at items 0/1. -/
theorem asTy_frmOf_zero {A B : CoreTy} (fr : Frame S A B) :
    asTy (itm (frmOf fr).xs 0) = A := by
  cases fr <;> rfl

theorem asTy_frmOf_one {A B : CoreTy} (fr : Frame S A B) :
    asTy (itm (frmOf fr).xs 1) = B := by
  cases fr <;> rfl

theorem beq_self_true (t : CoreTy) : (t == t) = true := CoreTy.beq_refl t

/-- `frameOk` accepts the `frmOf` encoding of any typed frame once the
    fuel covers its erased expressions (06 §13's per-clause checks are
    exactly the constructors' typings). -/
theorem frameOk_frmOf {p : RawProg} {A B : CoreTy} (fr : Frame (sigOf p) A B)
    (fuel : Int) (hf : ∀ e ∈ frExprs fr, (exprFuel e : Int) ≤ fuel) :
    frameOk fuel p (frmOf fr) = true := by
  cases fr with
  | letF env b =>
    have hb := hasTy_of_coreExpr b fuel (hf _ (List.mem_cons_self _ _))
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env, hb]
  | ifF env th el =>
    have hth := hasTy_of_coreExpr th fuel (hf _ (List.mem_cons_self _ _))
    have hel := hasTy_of_coreExpr el fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env,
      beq_self_true, hth, hel]
  | pairL env b =>
    have hb := hasTy_of_coreExpr b fuel (hf _ (List.mem_cons_self _ _))
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env,
      beq_self_true, hb]
  | pairR a =>
    simp [frameOk, frmOf, beq_self_true, valOk_of_coreVal a]
  | fstF => simp [frameOk, frmOf, beq_self_true]
  | sndF => simp [frameOk, frmOf, beq_self_true]
  | injF i h =>
    rename_i ts
    have hi : i < ts.length := by
      have := List.get?_eq_some.mp h
      obtain ⟨hi, -⟩ := this; exact hi
    have hdec : decide ((i : Int) < ts.length) = true :=
      decide_eq_true (by omega)
    have hgd : (ts[i]?).getD CoreTy.i64 = A := by
      have h' : ts[i]? = some A := by
        rw [← List.get?_eq_getElem?]; exact h
      rw [h']; rfl
    have htN : ((i : Int).toNat) = i := rfl
    simp [frameOk, frmOf, hdec, htN, hgd, beq_self_true]
    exact hi
  | matchF env bs =>
    rename_i ts
    have hbs := branches_all_of_Branches bs fuel hf
    have hlen : bs.erase.length = ts.length := Branches_erase_length bs
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env,
      tyL_tyItem, valL_valItem, exL_exItem, hlen, beq_self_eq_true, hbs]
  | recF fs pre post k heq env done rest =>
    have hdlen : done.erase.length = pre.length := by
      rw [CoreVals_erase_length, List.length_map]
    have hlt : decide (done.erase.length < fs.length) = true := by
      rw [hdlen, heq]
      rw [decide_eq_true_eq]
      rw [List.length_append, List.length_cons]; omega
    have hgd : ((fs[pre.length]?).getD ("", .i64)).2 = A := by
      rw [heq, List.getElem?_append_right (Nat.le_refl pre.length),
        Nat.sub_self, List.getElem?_cons_zero]
      rfl
    have htk : (fs.take pre.length).map Prod.snd = pre.map Prod.snd := by
      rw [heq, List.take_append_of_le_length (Nat.le_refl pre.length),
        List.take_length]
    have hdr : (fs.drop (pre.length + 1)).map Prod.snd =
        post.map Prod.snd := by
      rw [heq, List.drop_append, List.drop_one]
      rfl
    have hrest := exprsOk_of_Fields rest fuel hf
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env,
      valsOk_of_coreVals done, valL_valItem, exL_exItem, tyL_tyItem,
      hdlen, hlt, hgd, htk, hdr, hrest, beq_self_true]
    try rw [← hdlen]; exact of_decide_eq_true hlt
  | fieldF i k h =>
    rename_i fs
    have hi : i < fs.length := by
      obtain ⟨hi, -⟩ := List.get?_eq_some.mp h; exact hi
    have hdec : decide ((i : Int) < fs.length) = true :=
      decide_eq_true (by omega)
    have hgd : ((fs[i]?).getD ("", .i64)).2 = B := by
      have h' : fs[i]? = some (k, B) := by
        rw [← List.get?_eq_getElem?]; exact h
      rw [h']; rfl
    have htN : ((i : Int).toNat) = i := rfl
    simp [frameOk, frmOf, hdec, htN, hgd, beq_self_true]
    exact hi
  | consH env tl =>
    have htl := hasTy_of_coreExpr tl fuel (hf _ (List.mem_cons_self _ _))
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env,
      beq_self_true, htl]
  | consT h =>
    simp [frameOk, frmOf, beq_self_true, valOk_of_coreVal h]
  | foldL env init body =>
    have hi := hasTy_of_coreExpr init fuel (hf _ (List.mem_cons_self _ _))
    have hbo := hasTy_of_coreExpr body fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    simp [frameOk, loopOk, frmOf, valsOk_of_coreVals env, hi, hbo]
  | foldI env xs body =>
    have hbo := hasTy_of_coreExpr body fuel (hf _ (List.mem_cons_self _ _))
    have hxs : (xs.erase).all (fun v => valOk v _) = true :=
      coreList_all_valOk xs
    simp [frameOk, loopOk, frmOf, valsOk_of_coreVals env, tyL_tyItem,
      valL_valItem, beq_self_true, hxs, hbo]
  | fixI env limit stop step =>
    have hl := hasTy_of_coreExpr limit fuel (hf _ (List.mem_cons_self _ _))
    have hs := hasTy_of_coreExpr stop fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    have hp := hasTy_of_coreExpr step fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self _ _))))
    simp [frameOk, loopOk, fixSteps, frmOf, valsOk_of_coreVals env,
      beq_self_true, hl, hs, hp]
  | fixL env s stop step =>
    have hs := hasTy_of_coreExpr stop fuel (hf _ (List.mem_cons_self _ _))
    have hp := hasTy_of_coreExpr step fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    simp [frameOk, loopOk, fixSteps, fixState_fixTy, frmOf,
      valsOk_of_coreVals env, valOk_of_coreVal s, beq_self_true, hs, hp]
  | fixS env s left count hb stop step =>
    have hs := hasTy_of_coreExpr stop fuel (hf _ (List.mem_cons_self _ _))
    have hp := hasTy_of_coreExpr step fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    have hbd : fixBound left count = true :=
      decide_eq_true (by obtain ⟨h1, h2, h3⟩ := hb; omega)
    simp [frameOk, loopOk, fixSteps, fixState_fixTy, frmOf,
      valsOk_of_coreVals env, valOk_of_coreVal s, beq_self_true,
      hbd, hs, hp]
    try obtain ⟨h1, h2, h3⟩ := hb; omega
  | fixT env left count hb stop step =>
    have hs := hasTy_of_coreExpr stop fuel (hf _ (List.mem_cons_self _ _))
    have hp := hasTy_of_coreExpr step fuel
      (hf _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
    have hbd : fixBound left count = true :=
      decide_eq_true (by obtain ⟨h1, h2, h3⟩ := hb; omega)
    simp [frameOk, loopOk, fixSteps, frmOf,
      valsOk_of_coreVals env, beq_self_true, hbd, hs, hp]
    try obtain ⟨h1, h2, h3⟩ := hb; omega
  | primArgsF op pre post heq env done rest =>
    have hdlen : done.erase.length = pre.length := CoreVals_erase_length done
    have hlt : decide (done.erase.length < (primSig op).ps.length) = true := by
      rw [hdlen, heq, decide_eq_true_eq]
      rw [List.length_append, List.length_cons]; omega
    have hgd : ((primSig op).ps[pre.length]?).getD .i64 = A := by
      rw [heq, List.getElem?_append_right (Nat.le_refl pre.length),
        Nat.sub_self, List.getElem?_cons_zero]
      rfl
    have htk : ((primSig op).ps.take pre.length) = pre := by
      rw [heq, List.take_append_of_le_length (Nat.le_refl pre.length),
        List.take_length]
    have hdr : ((primSig op).ps.drop (pre.length + 1)) = post := by
      rw [heq, List.drop_append, List.drop_one]
      rfl
    have hrest := exprsOk_of_Args rest fuel hf
    simp [frameOk, argsOk, frmOf, valsOk_of_coreVals env,
      valsOk_of_coreVals done, valL_valItem, exL_exItem, tyL_tyItem,
      primOfString_primName, hdlen, hlt, hgd, htk, hdr, hrest,
      beq_self_true]
    try rw [← hdlen]; exact of_decide_eq_true hlt
  | callArgsF i fsg hfq pre post heq env done rest =>
    have hdlen : done.erase.length = pre.length := CoreVals_erase_length done
    obtain ⟨fd, hfd, hfdq⟩ : ∃ fd, p.fns.get? i = some fd ∧
        ⟨fd.params, fd.result⟩ = fsg := by
      have h' := hfq
      simp only [sigOf, List.get?_map] at h'
      cases hfg : p.fns.get? i with
      | none => rw [hfg] at h'; exact Option.noConfusion h'
      | some fd =>
        rw [hfg] at h'
        have h'' : (some fd).map (fun f => ⟨f.params, f.result⟩) =
            some fsg := h'
        rw [Option.map_some'] at h''
        exact ⟨fd, rfl, Option.some.inj h''⟩
    have hilen : i < p.fns.length := by
      obtain ⟨hi, -⟩ := List.get?_eq_some.mp hfd; exact hi
    have hdec : decide ((i : Int) < p.fns.length) = true :=
      decide_eq_true (by omega)
    have hfp : fd.params = fsg.params := congrArg (·.params) hfdq
    have hfr : fd.result = fsg.result := congrArg (·.result) hfdq
    have heq2 : fd.params = pre ++ A :: post := hfp.trans heq
    have h' : p.fns[i]? = some fd := by
      rw [← List.get?_eq_getElem?]; exact hfd
    have hfdv : p.fns[i] = fd := by
      obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.mp h'; exact e
    have hgd2 : (p.fns[i]?).getD ⟨[], .i64, .unknown 0⟩ = fd := by
      rw [h']; rfl
    have hlt : decide (pre.length < fd.params.length) = true := by
      rw [heq2, decide_eq_true_eq]
      rw [List.length_append, List.length_cons]; omega
    have hgd : (fd.params[pre.length]?).getD .i64 = A := by
      rw [heq2, List.getElem?_append_right (Nat.le_refl pre.length),
        Nat.sub_self, List.getElem?_cons_zero]
      rfl
    have htk : (fd.params.take pre.length) = pre := by
      rw [heq2, List.take_append_of_le_length (Nat.le_refl pre.length),
        List.take_length]
    have hdr : (fd.params.drop (pre.length + 1)) = post := by
      rw [heq2, List.drop_append, List.drop_one]
      rfl
    have hrest := exprsOk_of_Args rest fuel hf
    simp [frameOk, argsOk, frmOf, valsOk_of_coreVals env,
      valsOk_of_coreVals done, valL_valItem, exL_exItem, tyL_tyItem,
      hilen, hdec, hgd2, hfdv, hfr, hdlen, hlt, hgd, htk, hdr, hrest,
      beq_self_true]
    try exact ⟨of_decide_eq_true hlt, valsOk_of_coreVals done⟩
  | retF => simp [frameOk, frmOf, beq_self_true]
  | handleF r h env hd =>
    have hP : catalogPt p.catalog r = some _ := h
    have hhd := hasTy_of_coreExpr hd fuel (hf _ (List.mem_cons_self _ _))
    simp [frameOk, envOk, frmOf, valsOk_of_coreVals env, hP,
      beq_self_true, hhd]
  | raiseF r h =>
    have hP : catalogPt p.catalog r = some _ := h
    simp [frameOk, frmOf, hP, beq_self_true]

/-- `ctlTy` accepts the `ctlOf` encoding of a typed control at the
    control's own type. -/
theorem ctlTy_ctlOf {p : RawProg} {A : CoreTy} (c : Control (sigOf p) A)
    (fuel : Int) (hf : ∀ e ∈ ctlExprs c, (exprFuel e : Int) ≤ fuel) :
    ctlTy fuel p (ctlOf c) = .ok A := by
  cases c with
  | evalC env e =>
    obtain ⟨e', he'⟩ := elabE_of_coreExpr (fuelN fuel) e (by
      have hb := hf _ (List.mem_cons_self _ _)
      unfold fuelN; split
      · omega
      · have h2 : ((fuel.toNat : Int)) = fuel :=
          Int.toNat_of_nonneg (by omega)
        omega)
    unfold ctlTy
    dsimp only [ctlOf]
    rw [if_pos rfl]
    simp only [itm, List.getD_cons_zero, List.getD_cons_succ, asExpr]
    rw [tyL_tyItem, valL_valItem, valsOk_of_coreVals env, if_pos rfl, he']
  | retC v =>
    simp [ctlTy, ctlOf, asTy_ty, asVal_val, valOk_of_coreVal v]
  | raiseC r h v =>
    have hP : catalogPt p.catalog r = some _ := h
    simp [ctlTy, ctlOf, asTy_ty, asStr_str, asVal_val, hP,
      valOk_of_coreVal v]

/-- `cfgTy`'s frame-chain fold accepts `contOf k`, ending at the
    continuation's result type. -/
theorem contOk_fold {p : RawProg} : ∀ {A T : CoreTy} (k : Cont (sigOf p) A T)
    (fuel : Int) (hf : ∀ e ∈ contExprs k, (exprFuel e : Int) ≤ fuel),
    (contOf k).foldl (fun (acc : Except String CoreTy) fr =>
      match acc with
      | .error e => .error e
      | .ok cur =>
        if asTy (itm fr.xs 0) == cur then
          (if frameOk fuel p fr then .ok (asTy (itm fr.xs 1))
           else .error "[rcic_scm_cf_frame]")
        else .error "[rcic_scm_cf_chain]") (.ok A) = .ok T
  | _, _, .nil, _, _ => rfl
  | _, _, .cons fr k, fuel, hf => by
    have hfk : frameOk fuel p (frmOf fr) = true :=
      frameOk_frmOf fr fuel (fun e he => hf _ (List.mem_append_left _ he))
    have ih := contOk_fold k fuel
      (fun e he => hf _ (List.mem_append_right _ he))
    simp only [contOf, List.foldl_cons]
    rw [asTy_frmOf_zero, beq_self_true, if_pos rfl, hfk, if_pos rfl,
      asTy_frmOf_one]
    exact ih

/-- `cfgTy` accepts the `cfgOf` encoding of a typed configuration at its
    stored result type (06:412's `→` acceptance half). -/
theorem cfgTy_cfgOf {p : RawProg} {T : CoreTy} (c : Config (sigOf p) T)
    (fuel : Int)
    (hfctl : ∀ e ∈ ctlExprs c.ctl, (exprFuel e : Int) ≤ fuel)
    (hfk : ∀ e ∈ contExprs c.k, (exprFuel e : Int) ≤ fuel) :
    cfgTy fuel p (cfgOf c) = .ok T := by
  obtain ⟨A, ctl, k⟩ := c
  unfold cfgTy
  dsimp only [cfgOf]
  rw [ctlTy_ctlOf ctl fuel hfctl]
  dsimp only []
  show (match List.foldl (fun (acc : Except String CoreTy) fr =>
      match acc with
      | .error e => .error e
      | .ok cur =>
        if asTy (itm fr.xs 0) == cur then
          (if frameOk fuel p fr then .ok (asTy (itm fr.xs 1))
           else .error "[rcic_scm_cf_frame]")
        else .error "[rcic_scm_cf_chain]") (.ok A) (contOf k) with
    | .error e => .error e
    | .ok cur => if cur == T then .ok T else .error "[rcic_scm_cf_result]") =
      (.ok T : Except String CoreTy)
  rw [contOk_fold k fuel hfk]
  dsimp only []
  rw [beq_self_true, if_pos rfl]

/-- `finOk` accepts the `finOf` encoding of a typed final outcome. -/
theorem finOk_finOf {p : RawProg} {T : CoreTy} (o : Final (sigOf p) T) :
    finOk p (finOf o) = true := by
  cases o with
  | returned v =>
    simp [finOk, finOf, asVal_val, valOk_of_coreVal v]
  | raised r h v =>
    have hP : catalogPt p.catalog r = some _ := h
    simp [finOk, finOf, asStr_str, asVal_val, hP, valOk_of_coreVal v]

/-! ## Canonical-object producers (06 §19 `→`, carrier-acceptance half) -/

/-- `objDec` at kind 22 reads `encCfg` back — `cxDec_cxEnc` lifted through
    the object decoder's `kind > 21` dispatch. -/
theorem objDec_encCfg (c : CfgO)
    (hdq : dqCfgO c ((encCfg c).toList.length : Int)) :
    BoundProg.objDec ((encCfg c).length : Int) 22 (encCfg c) =
      .ok (.cx (.cfg c), (encCfg c).toList.length) := by
  unfold BoundProg.objDec
  rw [if_pos (by decide : (22 : Int) > 21)]
  rw [show encCfg c = cxEnc (.cfg c) from rfl]
  rw [show (((cxEnc (.cfg c)).length : Int)) = (encCfg c).toList.length
      from rfl]
  rw [cxDec_cxEnc 22 (.cfg c) _ ⟨hdq, by omega⟩ rfl]
  rfl

/-- `objDec` at kind 23 reads `encFin` back. -/
theorem objDec_encFin (f : FinO)
    (hdq : dqFinO f ((encFin f).toList.length : Int)) :
    BoundProg.objDec ((encFin f).length : Int) 23 (encFin f) =
      .ok (.cx (.fin f), (encFin f).toList.length) := by
  unfold BoundProg.objDec
  rw [if_pos (by decide : (23 : Int) > 21)]
  rw [show encFin f = cxEnc (.fin f) from rfl]
  rw [show (((cxEnc (.fin f)).length : Int)) = (encFin f).toList.length
      from rfl]
  rw [cxDec_cxEnc 23 (.fin f) _ ⟨hdq, by omega⟩ rfl]
  rfl

/-- `objDec` at kind 24 reads a run wrapper back. -/
theorem objDec_encRun (tag : Int) (m : CX)
    (hdq : dqCX (.run tag m)
      ((cxEnc (.run tag m)).toList.length : Int)) :
    BoundProg.objDec ((cxEnc (.run tag m)).length : Int) 24 (cxEnc (.run tag m)) =
      .ok (.cx (.run tag m), (cxEnc (.run tag m)).toList.length) := by
  unfold BoundProg.objDec
  rw [if_pos (by decide : (24 : Int) > 21)]
  rw [show (((cxEnc (.run tag m)).length : Int)) =
      (cxEnc (.run tag m)).toList.length from rfl]
  rw [cxDec_cxEnc 24 (.run tag m) _ hdq ⟨by decide, by decide⟩]
  rfl

/-- `cfgSchema.decode` accepts the encoded configuration object. -/
theorem cfgSchema_decode (c : CfgO)
    (hdq : dqCfgO c ((encCfg c).toList.length : Int)) :
    cfgSchema.decode (encCfg c) = some c := by
  show (match BoundProg.objDec ((encCfg c).length : Int) 22 (encCfg c) with
    | .ok (.cx (.cfg c'), _) => some c' | _ => none) = some c
  rw [objDec_encCfg c hdq]

/-- `finSchema.decode` accepts the encoded outcome object. -/
theorem finSchema_decode (f : FinO)
    (hdq : dqFinO f ((encFin f).toList.length : Int)) :
    finSchema.decode (encFin f) = some f := by
  show (match BoundProg.objDec ((encFin f).length : Int) 23 (encFin f) with
    | .ok (.cx (.fin f'), _) => some f' | _ => none) = some f
  rw [objDec_encFin f hdq]

/-- `runSchema.decode` accepts the encoded run wrapper. -/
theorem runSchema_decode (tag : Int) (m : CX)
    (hdq : dqCX (.run tag m)
      ((cxEnc (.run tag m)).toList.length : Int)) :
    runSchema.decode (cxEnc (.run tag m)) = some (tag, m) := by
  show (match BoundProg.objDec ((cxEnc (.run tag m)).length : Int) 24
      (cxEnc (.run tag m)) with
    | .ok (.cx (.run tag' m'), _) => some (tag', m') | _ => none) =
      some (tag, m)
  rw [objDec_encRun tag m hdq]

/-- The five `CanonicalObjectAt` conjuncts for an encoded configuration
    under the ref `⟨3, 22, derived⟩`: canonical decode (`cfgSchema_decode`),
    re-encode to the same bytes, class/kind consistency `3/22`, derived
    digest, and no trailing fields (`objDec` consumes the whole input). -/
theorem canonicalObjectAt_encCfg (c : CfgO)
    (hdq : dqCfgO c ((encCfg c).toList.length : Int)) :
    CanonicalObjectAt cfgSchema
      ⟨3, 22, Rcic.TypedRef.deriveDigest 3 22 (encCfg c)⟩ (encCfg c) := by
  have hd := cfgSchema_decode c hdq
  refine ⟨?_, rfl, ?_⟩
  · rw [hd]
    exact ⟨rfl, rfl⟩
  · show (match BoundProg.objDec ((encCfg c).length : Int) 22 (encCfg c) with
      | .ok (_, q) => q == (encCfg c).length | _ => false) = true
    rw [objDec_encCfg c hdq]
    simp
    exact rfl

/-- `CanonicalObjectAt` for an encoded final outcome at `⟨3, 23, …⟩`. -/
theorem canonicalObjectAt_encFin (f : FinO)
    (hdq : dqFinO f ((encFin f).toList.length : Int)) :
    CanonicalObjectAt finSchema
      ⟨3, 23, Rcic.TypedRef.deriveDigest 3 23 (encFin f)⟩ (encFin f) := by
  have hd := finSchema_decode f hdq
  refine ⟨?_, rfl, ?_⟩
  · rw [hd]
    exact ⟨rfl, rfl⟩
  · show (match BoundProg.objDec ((encFin f).length : Int) 23 (encFin f) with
      | .ok (_, q) => q == (encFin f).length | _ => false) = true
    rw [objDec_encFin f hdq]
    simp
    exact rfl

/-- `CanonicalObjectAt` for an encoded run wrapper at `⟨3, 24, …⟩`. -/
theorem canonicalObjectAt_encRun (tag : Int) (m : CX)
    (hdq : dqCX (.run tag m)
      ((cxEnc (.run tag m)).toList.length : Int)) :
    CanonicalObjectAt runSchema
      ⟨3, 24, Rcic.TypedRef.deriveDigest 3 24 (cxEnc (.run tag m))⟩
      (cxEnc (.run tag m)) := by
  have hd := runSchema_decode tag m hdq
  refine ⟨?_, rfl, ?_⟩
  · rw [hd]
    exact ⟨rfl, rfl⟩
  · show (match BoundProg.objDec ((cxEnc (.run tag m)).length : Int) 24
        (cxEnc (.run tag m)) with
      | .ok (_, q) => q == (cxEnc (.run tag m)).length | _ => false) = true
    rw [objDec_encRun tag m hdq]
    simp
    exact rfl

/-- 06 §19 `config_at` (06:412) `→` direction: a typed configuration whose
    wire image is `dqCfgO`-wellformed at its own encoding length and whose
    expressions fit `b.length` of fuel is a `ConfigAt` under the derived
    ref. -/
theorem configAt_of_wf {p : RawProg} {T : CoreTy} (c : Config (sigOf p) T)
    (hdq : dqCfgO (cfgOf c) ((encCfg (cfgOf c)).toList.length : Int))
    (hf : ∀ e ∈ ctlExprs c.ctl,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c)).toList.length)
    (hfk : ∀ e ∈ contExprs c.k,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c)).toList.length) :
    ConfigAt p ⟨3, 22, Rcic.TypedRef.deriveDigest 3 22 (encCfg (cfgOf c))⟩
      (encCfg (cfgOf c)) :=
  ⟨canonicalObjectAt_encCfg _ hdq, cfgOf c, cfgSchema_decode _ hdq,
    cfgTy_cfgOf c _ hf hfk⟩

/-- 06 §19 `outcome_at` (06:413) `→` direction. -/
theorem outcomeAt_of_wf {p : RawProg} {T : CoreTy} (o : Final (sigOf p) T)
    (hdq : dqFinO (finOf o) ((encFin (finOf o)).toList.length : Int)) :
    OutcomeAt p ⟨3, 23, Rcic.TypedRef.deriveDigest 3 23 (encFin (finOf o))⟩
      (encFin (finOf o)) :=
  ⟨canonicalObjectAt_encFin _ hdq, finOf o, finSchema_decode _ hdq,
    finOk_finOf o⟩

/-- `RunResultAt` for an encoded run wrapper whose member passes
    `runMemberOk`. -/
theorem runResultAt_of_member {p : RawProg} (tag : Int) (m : CX)
    (hdq : dqCX (.run tag m)
      ((cxEnc (.run tag m)).toList.length : Int))
    (hm : runMemberOk p ((cxEnc (.run tag m)).toList.length) tag m) :
    RunResultAt p
      ⟨3, 24, Rcic.TypedRef.deriveDigest 3 24 (cxEnc (.run tag m))⟩
      (cxEnc (.run tag m)) :=
  ⟨canonicalObjectAt_encRun tag m hdq, tag, m, runSchema_decode tag m hdq,
    hm⟩

/-- 06 §19 `scm_step_at` (06:414) `→` direction: an intrinsic `SCMStep`
    between well-formed encoded endpoints is a bound `SCMStepAt`. -/
theorem scmStepAt_of_step {profile : String} {P : BoundCoreProgram profile}
    {T : CoreTy} (c c' : Config (sigOf P.prog) T)
    {out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy}
    {F : Int}
    (hchk : progCheck F P.prog = .ok out)
    (hci : dqCfgO (cfgOf c) ((encCfg (cfgOf c)).toList.length : Int))
    (hfi : ∀ e ∈ ctlExprs c.ctl,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c)).toList.length)
    (hfik : ∀ e ∈ contExprs c.k,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c)).toList.length)
    (hco : dqCfgO (cfgOf c') ((encCfg (cfgOf c')).toList.length : Int))
    (hfo : ∀ e ∈ ctlExprs c'.ctl,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c')).toList.length)
    (hfok : ∀ e ∈ contExprs c'.k,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c')).toList.length)
    (hst : SCMStep out.1 c c') :
    SCMStepAt P
      ⟨3, 22, Rcic.TypedRef.deriveDigest 3 22 (encCfg (cfgOf c))⟩
      (encCfg (cfgOf c))
      ⟨3, 22, Rcic.TypedRef.deriveDigest 3 22 (encCfg (cfgOf c'))⟩
      (encCfg (cfgOf c')) :=
  ⟨T, c, c', out, F, cfgOf c, cfgOf c', hchk,
    configAt_of_wf c hci hfi hfik, cfgSchema_decode _ hci,
    cfgToRaw_cfgOf c,
    configAt_of_wf c' hco hfo hfok, cfgSchema_decode _ hco,
    cfgToRaw_cfgOf c', hst⟩

/-- 06 §19 `scm_runs_at` (06:415) `→` direction: an intrinsic `n`-step run
    between a well-formed encoded start and a run-related endpoint member
    is a bound `SCMRunsAt`. -/
theorem scmRunsAt_of_runs {profile : String} {P : BoundCoreProgram profile}
    {T : CoreTy} (c c' : Config (sigOf P.prog) T) (n : Nat)
    {out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy}
    {F : Int} (tag : Int) (m : CX)
    (hchk : progCheck F P.prog = .ok out)
    (hci : dqCfgO (cfgOf c) ((encCfg (cfgOf c)).toList.length : Int))
    (hfi : ∀ e ∈ ctlExprs c.ctl,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c)).toList.length)
    (hfik : ∀ e ∈ contExprs c.k,
      (exprFuel e : Int) ≤ (encCfg (cfgOf c)).toList.length)
    (hrq : dqCX (.run tag m)
      ((cxEnc (.run tag m)).toList.length : Int))
    (hmbr : runMemberOk P.prog ((cxEnc (.run tag m)).toList.length) tag m)
    (hrel : runResultRel c' tag m)
    (hruns : SCMRuns out.1 n c c') :
    SCMRunsAt P n
      ⟨3, 22, Rcic.TypedRef.deriveDigest 3 22 (encCfg (cfgOf c))⟩
      (encCfg (cfgOf c))
      ⟨3, 24, Rcic.TypedRef.deriveDigest 3 24 (cxEnc (.run tag m))⟩
      (cxEnc (.run tag m)) :=
  ⟨T, c, c', out, F, cfgOf c, tag, m, hchk,
    configAt_of_wf c hci hfi hfik, cfgSchema_decode _ hci,
    cfgToRaw_cfgOf c,
    runResultAt_of_member tag m hrq hmbr, runSchema_decode tag m hrq,
    hrel, hruns⟩

/-- 06 §19 `entry_runs_at` (06:416/419) `→` direction: `SCMRuns` from the
    typed entry configuration plus `argsValueAt` arguments is a bound
    `EntryRunsAt`. -/
theorem entryRunsAt_of_runs {profile : String} {P : BoundCoreProgram profile}
    {argBytes : List String} (n : Nat)
    {out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy}
    {F : Int} {ef : FnSig}
    (hchk : progCheck F P.prog = .ok out)
    (hf : (sigOf P.prog).fns.get? P.prog.entry.toNat = some ef)
    (env : CoreVals ef.params) (hargs : argsValueAt ef.params argBytes)
    (c' : Config (sigOf P.prog) ef.result) (tag : Int) (m : CX)
    (hrq : dqCX (.run tag m)
      ((cxEnc (.run tag m)).toList.length : Int))
    (hmbr : runMemberOk P.prog ((cxEnc (.run tag m)).toList.length) tag m)
    (hrel : runResultRel c' tag m)
    (hr : SCMRuns out.1 n
      ⟨ef.result, .evalC env (out.1.at P.prog.entry.toNat ef hf), .nil⟩ c') :
    EntryRunsAt P argBytes n
      ⟨3, 24, Rcic.TypedRef.deriveDigest 3 24 (cxEnc (.run tag m))⟩
      (cxEnc (.run tag m)) :=
  ⟨out, F, ef, hf, env, c', tag, m, hchk, hargs,
    runResultAt_of_member tag m hrq hmbr, runSchema_decode tag m hrq,
    hrel, hr⟩

/-! ## Pins -/

namespace Pins

open Rcic.Scm.Raw Rcic.Scm.CfgAt.Pins Rcic.Scm.Erase

/-- Kind-22 decode at `Option CfgO` (the `schema.Obj` projection does not
    reduce for `==`'s instance search). -/
def cfgDecW (b : String) : Option CfgO := cfgSchema.decode b

/-- Kind-23 decode at `Option FinO`. -/
def finDecW (b : String) : Option FinO := finSchema.decode b

/-- A concrete `CoreVal` fixture (`ScmElabErase`'s `five`). -/
def fiveI : CoreVal .i64 := .i64V 5 ⟨by decide, by decide⟩

/-- `retC` of `fiveI` — the simplest typed control. -/
def ctlRetI : Control ⟨[], [], []⟩ .i64 := .retC fiveI

/-- A `letF` frame binding an `i64` literal — a real non-trivial frame
    (env + scoped body), not a degenerate nullary one. -/
def frLetI : Frame ⟨[], [], []⟩ .i64 .i64 := .letF .nil (.lit fiveI)

/-- A `foldL` frame — a loop-family frame with two erased bodies. -/
def frFoldI : Frame ⟨[], [], []⟩ (.list .i64) .i64 :=
  .foldL .nil (.lit fiveI) (.lit fiveI)

/-- The configuration `⟨retC fiveI, [letF]⟩` at result `i64`. -/
def cfgRetI : Config ⟨[], [], []⟩ .i64 := ⟨.i64, .retC fiveI, .cons frLetI .nil⟩

/-- The returned outcome `(.i 5)`. -/
def finRetI : Final ⟨[], [], []⟩ .i64 := .returned fiveI

-- Encoder shapes.
#guard ctlOf ctlRetI == ⟨1, [.ty .i64, .val (.i 5)]⟩
#guard frmOf frLetI ==
  ⟨0, [.ty .i64, .ty .i64, tyItem [], valItem [], .expr (.lit (.i 5) .i64)]⟩
#guard cfgOf cfgRetI ==
  ⟨.i64, ⟨1, [.ty .i64, .val (.i 5)]⟩,
    [⟨0, [.ty .i64, .ty .i64, tyItem [], valItem [], .expr (.lit (.i 5) .i64)]⟩]⟩
#guard finOf finRetI == ⟨.i64, 0, [.val (.i 5)]⟩

-- Raw roundtrips on the concrete objects.
#guard ctlToRaw (ctlOf ctlRetI) == .retC (.i 5)
#guard frmToRaw (frmOf frLetI) == .letF [] (.lit (.i 5) .i64)
#guard frmToRaw (frmOf frFoldI) ==
  .foldL [] (.lit (.i 5) .i64) (.lit (.i 5) .i64)
#guard cfgToRaw (cfgOf cfgRetI) ==
  ⟨.retC (.i 5), [.letF [] (.lit (.i 5) .i64)]⟩
#guard finToRaw (finOf finRetI) == (1, .i 5, "")

-- The encoders agree with the typed erasures (theorem-level, `by …`).
example : cfgToRaw (cfgOf cfgRetI) = cfgRetI.erase := cfgToRaw_cfgOf cfgRetI
example : finToRaw (finOf finRetI) = finalErase finRetI := finToRaw_finOf finRetI

-- The canonical bytes of an encoded configuration decode back to the
-- same `CfgO` — the wire-level roundtrip the `ConfigAt` direction needs.
#guard cfgDecW (cfgSchema.encode (cfgOf cfgRetI)) == some (cfgOf cfgRetI)
#guard finDecW (finSchema.encode (finOf finRetI)) == some (finOf finRetI)

-- Member teeth at the pin level: a `.cfg` member at tag 0 and a `.fin`
-- member at tag 1 both refuse.
#guard (runToRaw 0 (.cfg (cfgOf cfgRetI)) : Option RawRunResult) == none
#guard (runToRaw 1 (.fin (finOf finRetI)) : Option RawRunResult) == none
#guard runToRaw 1 (.cfg (cfgOf cfgRetI)) ==
  some (.suspended ⟨.retC (.i 5), [.letF [] (.lit (.i 5) .i64)]⟩)
#guard runToRaw 0 (.fin (finOf finRetI)) == some (.done 1 (.i 5) "")

end Pins

end Rcic.Scm.BoundBridge
