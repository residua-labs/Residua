/-
RCIC 06 §13 / §15 — the intrinsic machine and the first-order machine
agree step for step (#6029 K3, segment 6).

Owner text: 06 §13 "The first-order wire configuration stores closed tags and
payloads. Its decoder reconstructs a raw configuration and validates the
frame-chain typing before producing the typed semantic configuration." 06 §19
"intrinsic SCMStep → SCMStepAt; … entry initialization/final-outcome
correspondence".

`Raw.step` is the first-order machine pinned to the carrier `rcic-scm-core`;
`stepI` is the typed machine. For a typed program whose bodies erase to the
raw program's bodies (`ElabErase.elabBodies_erase` gives this for every
elaborated program):
  `evalI_sim`, `raiseI_sim` — an eval / raising step of the typed machine is
     the raw step of the erased configuration, exactly;
  `retI_sim` — a returning step likewise, except that the raw machine also
     refuses a primitive whose first string argument exceeds the carrier's
     2048-scalar bound (`primBound`), where the typed law has no bound; that
     is the one place the raw step may be the stuck refusal instead
     (`[model_note]`, the carrier's recorded bound, not a 06 rule).
-/
import rcic.ScmElabErase
import rcic.ScmProgress
import rcic.ScmRawRelations
import rcic.ScmNoStuck

namespace Rcic.Scm.Sim
open Rcic.Scm Rcic.Scm.Erase Rcic.Scm.ElabErase

variable {S : Sig}

/-! ## Erasure lemmas -/

theorem nth_ofNat {α : Type} (xs : List α) (i : Nat) : Raw.nth? xs (i : Int) = xs.get? i := by
  unfold Raw.nth?
  rw [if_neg (Int.not_lt.mpr (Int.ofNat_nonneg i)), Int.toNat_ofNat]

theorem vals_get_erase : ∀ {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) (i : Nat) (h : Γ.get? i = some T),
    env.erase.get? i = some (env.get i h).erase
  | _ :: _, _, .cons x _, 0, h => by
      have e := Option.some.inj h; subst e; rfl
  | _ :: _, _, .cons _ xs, n + 1, h => vals_get_erase xs n h
  | [], _, .nil, _, h => nomatch h

theorem branches_at_erase {Γ : List CoreTy} {T : CoreTy} :
    ∀ {ts : List CoreTy} {A : CoreTy} (bs : Branches S Γ ts T) (i : Nat) (h : ts.get? i = some A),
    bs.erase.get? i = some (bs.at i h).erase
  | _ :: _, _, .cons b _, 0, h => by
      have e := Option.some.inj h; subst e; rfl
  | _ :: _, _, .cons _ bs, n + 1, h => branches_at_erase bs n h
  | [], _, .nil, _, h => nomatch h

theorem recordField_erase : ∀ (fs : List (String × CoreTy)) {k : String} {A : CoreTy}
    (xs : CoreVals (fs.map Prod.snd)) (i : Nat) (h : fs.get? i = some (k, A)),
    xs.erase.get? i = some (recordField fs xs i h).erase
  | (_, _) :: _, _, _, .cons x _, 0, h => by
      have e := (Prod.mk.inj (Option.some.inj h)).2; subst e; rfl
  | _ :: fs, _, _, .cons _ xs, n + 1, h => recordField_erase fs xs n h
  | [], _, _, _, _, h => nomatch h

theorem snoc_erase : ∀ {ts : List CoreTy} {A : CoreTy} (xs : CoreVals ts) (v : CoreVal A),
    (xs.snoc v).erase = xs.erase ++ [v.erase]
  | _, _, .nil, _ => rfl
  | _, _, .cons x xs, v => by
      show x.erase :: (xs.snoc v).erase = x.erase :: (xs.erase ++ [v.erase])
      rw [snoc_erase xs v]

theorem vals_cast_erase : ∀ {ts ts' : List CoreTy} (h : ts = ts') (xs : CoreVals ts),
    (h ▸ xs : CoreVals ts').erase = xs.erase := by
  intro ts ts' h xs; subst h; rfl

theorem val_cast_erase : ∀ {t t' : CoreTy} (h : t = t') (v : CoreVal t),
    (h ▸ v : CoreVal t').erase = v.erase := by
  intro t t' h v; subst h; rfl

theorem body_at_erase (p : RawProg) (prog : Bodies S S.fns)
    (hp : Bodies.erasures prog = p.fns.map RawFnDef.body) (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f) :
    ∃ fd : RawFnDef, p.fns.get? i = some fd ∧ fd.body = (prog.at i f hf).erase := by
  have h1 := bodies_at_erase prog i f hf
  rw [hp, List.get?_eq_getElem?, List.getElem?_map, ← List.get?_eq_getElem?] at h1
  cases hfd : p.fns.get? i with
  | none => rw [hfd] at h1; exact Option.noConfusion h1
  | some fd => rw [hfd] at h1; exact ⟨fd, rfl, Option.some.inj h1⟩

theorem enter_sim (p : RawProg) (prog : Bodies S S.fns)
    (hp : Bodies.erasures prog = p.fns.map RawFnDef.body) {T : CoreTy} (i : Nat) (f : FnSig)
    (hf : S.fns.get? i = some f) (args : CoreVals f.params) (k : Cont S f.result T) (c' : Config S T)
    (h : enterI prog i f hf args k = .next c') :
    Raw.enter p (i : Int) args.erase k.erase = Raw.next c'.erase := by
  have e := StepResult.next.inj h; subst e
  obtain ⟨fd, hfd, hbody⟩ := body_at_erase p prog hp i f hf
  unfold Raw.enter
  rw [nth_ofNat, hfd]
  show Raw.evalTo args.erase fd.body (.retF :: k.erase) = _
  rw [hbody]
  rfl

/-! ## Eval steps -/

theorem evalI_sim (p : RawProg) (prog : Bodies S S.fns)
    (hp : Bodies.erasures prog = p.fns.map RawFnDef.body) {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) :
    ∀ {A : CoreTy} (e : CoreExpr S Γ A) (k : Cont S A T) (c' : Config S T),
    evalI prog env e k = .next c' → Raw.evalStep p env.erase e.erase k.erase = Raw.next c'.erase := by
  intro A e k c' h
  cases e with
  | var i hi =>
    have e := StepResult.next.inj h; subst e
    show (match Raw.nth? env.erase (i : Int) with
      | some v => Raw.retTo v k.erase
      | none => Raw.stuck) = _
    rw [nth_ofNat, vals_get_erase env i hi]
    rfl
  | recordE xs hk =>
    cases xs with
    | nil => have e := StepResult.next.inj h; subst e; rfl
    | cons key x rest => have e := StepResult.next.inj h; subst e; rfl
  | prim op args =>
    have key : ∀ (ps : List CoreTy) (heq : (primSig op).ps = ps) (args : Args S Γ ps),
        pushPrim op env ps heq args k = .next c' →
        Raw.evalStep p env.erase (.prim (primName op) args.erase) k.erase = Raw.next c'.erase := by
      intro ps heq args h
      cases args with
      | nil => exact StepResult.noConfusion h
      | cons x rest => have e := StepResult.next.inj h; subst e; rfl
    exact key _ rfl args h
  | call f args =>
    cases f with
    | «local» i fs hf =>
      have key : ∀ (ps : List CoreTy) (heq : fs.params = ps) (args : Args S Γ ps),
          pushCall prog i fs hf env ps heq args k = .next c' →
          Raw.evalStep p env.erase (.call (.local (i : Int)) args.erase) k.erase = Raw.next c'.erase := by
        intro ps heq args h
        cases args with
        | nil =>
          have hs := enter_sim p prog hp i fs hf (heq ▸ CoreVals.nil) k c' h
          rw [vals_cast_erase] at hs
          exact hs
        | cons x rest => have e := StepResult.next.inj h; subst e; rfl
      exact key _ rfl args h
    | external r ex hx => exact StepResult.noConfusion h
  | _ => have e := StepResult.next.inj h; subst e; rfl

/-! ## Primitive execution agrees -/

theorem primOfString_primName (op : PrimOp) : primOfString (primName op) = some op := by
  cases op <;> rfl

theorem eqrec_vals_erase {a b : List CoreTy} (h : a = b) (xs : CoreVals a) :
    (Eq.rec (motive := fun x _ => CoreVals x) xs h).erase = xs.erase := by
  subst h; rfl

theorem scmPrim_sim (op : PrimOp) (vals : CoreVals (primSig op).ps)
    (hb : ¬ firstStrLen vals.erase > primBound) :
    scmPrim 0 (primName op) vals.erase 0 = PrimOut.ofLaw (primLaw op vals) (primCost (primSig op).varSize vals.erase) := by
  unfold scmPrim
  rw [if_neg (fun h => h.1 rfl), primOfString_primName op]
  show (match toCoreVals (primSig op).ps vals.erase with
    | none => PrimOut.refuse "[rcic_scm_prim_ill_typed]"
    | some xs =>
      if firstStrLen vals.erase > primBound then PrimOut.refuse "[rcic_scm_prim_bound]" else
      if (0 : Int) = 1 then
        (if (0 : Int) < 0 then PrimOut.refuse "[rcic_scm_prim_budget]"
         else if (0 : Int) < primCost (primSig op).varSize vals.erase then ⟨1, 2, unitRaw, "", 0, ""⟩
         else .ofLaw (primLaw op xs) (primCost (primSig op).varSize vals.erase))
      else .ofLaw (primLaw op xs) (primCost (primSig op).varSize vals.erase)) = _
  rw [erase_toCoreVals vals]
  show (if firstStrLen vals.erase > primBound then PrimOut.refuse "[rcic_scm_prim_bound]" else _) = _
  rw [if_neg hb]
  rfl

theorem scmPrim_bound (op : PrimOp) (vals : CoreVals (primSig op).ps)
    (hb : firstStrLen vals.erase > primBound) :
    scmPrim 0 (primName op) vals.erase 0 = PrimOut.refuse "[rcic_scm_prim_bound]" := by
  unfold scmPrim
  rw [if_neg (fun h => h.1 rfl), primOfString_primName op]
  show (match toCoreVals (primSig op).ps vals.erase with
    | none => PrimOut.refuse "[rcic_scm_prim_ill_typed]"
    | some xs =>
      if firstStrLen vals.erase > primBound then PrimOut.refuse "[rcic_scm_prim_bound]" else
      if (0 : Int) = 1 then
        (if (0 : Int) < 0 then PrimOut.refuse "[rcic_scm_prim_budget]"
         else if (0 : Int) < primCost (primSig op).varSize vals.erase then ⟨1, 2, unitRaw, "", 0, ""⟩
         else .ofLaw (primLaw op xs) (primCost (primSig op).varSize vals.erase))
      else .ofLaw (primLaw op xs) (primCost (primSig op).varSize vals.erase)) = _
  rw [erase_toCoreVals vals]
  show (if firstStrLen vals.erase > primBound then PrimOut.refuse "[rcic_scm_prim_bound]" else _) = _
  rw [if_pos hb]

theorem retPrim_raw (p : RawProg) (v : Val) (env : List Val) (name : String) (done : List Val)
    (rest : List Raw.Frame) :
    Raw.retStep p v (.argsF env 0 name 0 done [] :: rest) =
      (let o := scmPrim 0 name (done ++ [v]) 0
       if o.ok = 0 then Raw.stuck else if o.kind = 0 then Raw.retTo o.v rest else Raw.raiseTo o.r o.v rest) :=
  rfl

theorem raiseUnit_sim {B T : CoreTy} (r : RaisedRef) (rest : Cont S B T) (c' : Config S T)
    (h : raiseUnit r rest = .next c') : Raw.next c'.erase = Raw.raiseTo r unitRaw rest.erase := by
  unfold raiseUnit at h
  split at h
  · exact StepResult.noConfusion h
  · split at h
    · rename_i hp
      have e := StepResult.next.inj h; subst e; subst hp; rfl
    · exact StepResult.noConfusion h

/-! ## Return steps -/

theorem retI_sim (p : RawProg) (prog : Bodies S S.fns)
    (hp : Bodies.erasures prog = p.fns.map RawFnDef.body) {T : CoreTy} :
    ∀ {A : CoreTy} (v : CoreVal A) (k : Cont S A T) (c' : Config S T), retI prog v k = .next c' →
    Raw.retStep p v.erase k.erase = Raw.next c'.erase ∨ Raw.retStep p v.erase k.erase = Raw.stuck := by
  intro A v k c' h
  cases k with
  | nil => exact StepResult.noConfusion h
  | cons fr rest =>
    cases fr with
    | ifF env th el =>
      cases v with
      | boolV c => cases c <;> (have e := StepResult.next.inj h; subst e; exact Or.inl rfl)
    | fstF => cases v; have e := StepResult.next.inj h; subst e; exact Or.inl rfl
    | sndF => cases v; have e := StepResult.next.inj h; subst e; exact Or.inl rfl
    | matchF env bs =>
      cases v with
      | injV i A' hi w =>
        have e := StepResult.next.inj h; subst e
        left
        show (match Raw.nth? bs.erase (i : Int) with
          | some b => Raw.evalTo (w.erase :: env.erase) b rest.erase
          | none => Raw.stuck) = _
        rw [nth_ofNat, branches_at_erase bs i hi]
        rfl
    | recF fs pre post key heq env done more =>
      subst heq
      cases more with
      | nil =>
        have e := StepResult.next.inj h; subst e
        left
        show Raw.retTo (.r (done.erase ++ [v.erase])) rest.erase = Raw.next ⟨.retC (Val.r (Eq.rec (motive := fun x _ => CoreVals x) (done.snoc v) _).erase), rest.erase⟩
        rw [eqrec_vals_erase, snoc_erase]
        rfl
      | cons key2 x more' =>
        have e := StepResult.next.inj h; subst e
        left
        show Raw.evalTo env.erase x.erase (.recF env.erase (done.erase ++ [v.erase]) more'.erase :: rest.erase) =
          Raw.next ⟨.evalC env.erase x.erase,
            .recF env.erase (Eq.rec (motive := fun x _ => CoreVals x) (done.snoc v) _).erase more'.erase :: rest.erase⟩
        rw [eqrec_vals_erase, snoc_erase]
        rfl
    | fieldF i key hi =>
      cases v with
      | recordV xs =>
        have e := StepResult.next.inj h; subst e
        left
        show (match Raw.nth? xs.erase (i : Int) with
          | some x => Raw.retTo x rest.erase
          | none => Raw.stuck) = _
        rw [nth_ofNat, recordField_erase _ xs i hi]
        rfl
    | consT hd => cases v; have e := StepResult.next.inj h; subst e; exact Or.inl rfl
    | foldL env init body => cases v; have e := StepResult.next.inj h; subst e; exact Or.inl rfl
    | foldI env xs body =>
      cases xs <;> (have e := StepResult.next.inj h; subst e; exact Or.inl rfl)
    | fixL env s stop step =>
      cases v with
      | i64V n hn =>
        dsimp only [retI] at h
        split at h
        · rename_i hlt
          left
          show (if n < 0 then Raw.raiseTo "negative_loop_bound" unitRaw rest.erase else _) = _
          rw [if_pos hlt, raiseUnit_sim "negative_loop_bound" rest c' h]
        · rename_i hlt
          have e := StepResult.next.inj h; subst e
          left
          show (if n < 0 then _ else Raw.evalTo (s.erase :: env.erase) stop.erase
            (.fixS env.erase s.erase n 0 stop.erase step.erase :: rest.erase)) = _
          rw [if_neg hlt]
          rfl
    | fixS env s left count hb stop step =>
      cases v with
      | boolV c =>
        cases c with
        | true => have e := StepResult.next.inj h; subst e; exact Or.inl rfl
        | false =>
          dsimp only [retI] at h
          split at h
          · rename_i hc; exact absurd hc (by decide)
          · split at h
            · rename_i hz
              have e := StepResult.next.inj h; subst e
              left
              show (if (0 : Int) = 1 then Raw.retTo (Raw.fixOut 1 s.erase count) rest.erase
                else if left = 0 then Raw.retTo (Raw.fixOut 0 s.erase count) rest.erase
                else Raw.evalTo (s.erase :: env.erase) step.erase
                  (.fixT env.erase (left - 1) (count + 1) stop.erase step.erase :: rest.erase)) = _
              rw [if_neg (by decide), if_pos hz]
              rfl
            · rename_i hz
              have e := StepResult.next.inj h; subst e
              left
              show (if (0 : Int) = 1 then Raw.retTo (Raw.fixOut 1 s.erase count) rest.erase
                else if left = 0 then Raw.retTo (Raw.fixOut 0 s.erase count) rest.erase
                else Raw.evalTo (s.erase :: env.erase) step.erase
                  (.fixT env.erase (left - 1) (count + 1) stop.erase step.erase :: rest.erase)) = _
              rw [if_neg (by decide), if_neg hz]
              rfl
    | primArgsF op pre post heq env done more =>
      cases more with
      | nil =>
        have hraw : Raw.retStep p v.erase (Cont.cons (Frame.primArgsF op pre [] heq env done Args.nil) rest).erase =
            (let o := scmPrim 0 (primName op) (done.erase ++ [v.erase]) 0
             if o.ok = 0 then Raw.stuck else if o.kind = 0 then Raw.retTo o.v rest.erase
             else Raw.raiseTo o.r o.v rest.erase) := retPrim_raw p v.erase env.erase (primName op) done.erase rest.erase
        rw [hraw]
        have hv : done.erase ++ [v.erase] = (Eq.rec (motive := fun x _ => CoreVals x) (done.snoc v) heq.symm).erase := by
          rw [eqrec_vals_erase, snoc_erase]
        by_cases hb : firstStrLen (Eq.rec (motive := fun x _ => CoreVals x) (done.snoc v) heq.symm).erase > primBound
        · right
          have hb2 := scmPrim_bound op _ hb
          rw [← hv] at hb2
          rw [hb2]
          rfl
        · have hs := scmPrim_sim op _ hb
          rw [← hv] at hs
          rw [hs]
          dsimp only [retI] at h
          split at h
          · rename_i w hlaw
            have e := StepResult.next.inj h; subst e
            left
            rw [hlaw]
            rfl
          · rename_i r hlaw
            left
            rw [hlaw, raiseUnit_sim r rest c' h]
            rfl
      | cons x more' =>
        have e := StepResult.next.inj h; subst e
        left
        show Raw.evalTo env.erase x.erase (.argsF env.erase 0 (primName op) 0 (done.erase ++ [v.erase]) more'.erase :: rest.erase) =
          Raw.next ⟨.evalC env.erase x.erase, .argsF env.erase 0 (primName op) 0 (done.snoc v).erase more'.erase :: rest.erase⟩
        rw [snoc_erase]
        rfl
    | callArgsF i f hf pre post heq env done more =>
      cases more with
      | nil =>
        left
        have hs := enter_sim p prog hp i f hf _ rest c' h
        rw [eqrec_vals_erase, snoc_erase] at hs
        exact hs
      | cons x more' =>
        have e := StepResult.next.inj h; subst e
        left
        show Raw.evalTo env.erase x.erase (.argsF env.erase 1 "" (i : Int) (done.erase ++ [v.erase]) more'.erase :: rest.erase) =
          Raw.next ⟨.evalC env.erase x.erase, .argsF env.erase 1 "" (i : Int) (done.snoc v).erase more'.erase :: rest.erase⟩
        rw [snoc_erase]
        rfl
    | _ => have e := StepResult.next.inj h; subst e; exact Or.inl rfl

/-! ## Raising steps -/

theorem eqrec_val_erase {a b : CoreTy} (h : a = b) (v : CoreVal a) :
    (Eq.rec (motive := fun x _ => CoreVal x) v h).erase = v.erase := by
  subst h; rfl

theorem raiseI_sim {A T P : CoreTy} (r : RaisedRef) (hr : catalogPt S.catalog r = some P) (v : CoreVal P) :
    ∀ (k : Cont S A T) (c' : Config S T), raiseI r hr v k = .next c' →
    Raw.raiseStep r v.erase k.erase = Raw.next c'.erase := by
  intro k c' h
  cases k with
  | nil => exact StepResult.noConfusion h
  | cons fr rest =>
    cases fr with
    | handleF r' h' env hd =>
      unfold raiseI at h
      dsimp only at h
      split at h
      · rename_i hrr
        have e := StepResult.next.inj h; subst e
        show (if r' = r then Raw.evalTo (v.erase :: env.erase) hd.erase rest.erase
          else Raw.raiseTo r v.erase rest.erase) = _
        rw [if_pos hrr]
        show Raw.next ⟨.evalC (v.erase :: env.erase) hd.erase, rest.erase⟩ =
          Raw.next ⟨.evalC ((Eq.rec (motive := fun x _ => CoreVal x) v _).erase :: env.erase) hd.erase, rest.erase⟩
        rw [eqrec_val_erase]
      · rename_i hrr
        have e := StepResult.next.inj h; subst e
        show (if r' = r then Raw.evalTo (v.erase :: env.erase) hd.erase rest.erase
          else Raw.raiseTo r v.erase rest.erase) = _
        rw [if_neg hrr]
        rfl
    | _ => have e := StepResult.next.inj h; subst e; rfl

/-! ## The step simulation -/

/-- A final outcome as the raw machine reports it. -/
def finalOut {T : CoreTy} : Final S T → Raw.Out
  | .returned v => Raw.final 1 v.erase ""
  | .raised r _ v => Raw.final 2 v.erase r

/-- Simulation (first-order analogue of 06 §19 "intrinsic SCMStep → SCMStepAt"; not that clause, K3c), one step: a typed step is the raw
    step of the erased configuration (up to the carrier's primitive string
    bound, where the raw step is the stuck refusal). -/
theorem step_sim (p : RawProg) (prog : Bodies S S.fns) (hp : Bodies.erasures prog = p.fns.map RawFnDef.body)
    {T : CoreTy} (c c' : Config S T) (h : stepI prog c = .next c') :
    Raw.step p c.erase = Raw.next c'.erase ∨ Raw.step p c.erase = Raw.stuck :=
  match c, h with
  | ⟨_, .evalC env e, k⟩, h => Or.inl (evalI_sim p prog hp env e k c' h)
  | ⟨_, .retC v, k⟩, h => retI_sim p prog hp v k c' h
  | ⟨_, .raiseC r hr v, k⟩, h => Or.inl (raiseI_sim r hr v k c' h)

theorem evalI_not_final {Γ : List CoreTy} {T : CoreTy} (prog : Bodies S S.fns) (env : CoreVals Γ) :
    ∀ {A : CoreTy} (e : CoreExpr S Γ A) (k : Cont S A T) (o : Final S T), evalI prog env e k ≠ .final o := by
  intro A e k o h
  cases e with
  | recordE xs hk => cases xs <;> exact StepResult.noConfusion h
  | prim op args =>
    have key : ∀ (ps : List CoreTy) (heq : (primSig op).ps = ps) (args : Args S Γ ps),
        pushPrim op env ps heq args k ≠ .final o := by
      intro ps heq args h; cases args <;> exact StepResult.noConfusion h
    exact key _ rfl args h
  | call f args =>
    cases f with
    | «local» i fs hf =>
      have key : ∀ (ps : List CoreTy) (heq : fs.params = ps) (args : Args S Γ ps),
          pushCall prog i fs hf env ps heq args k ≠ .final o := by
        intro ps heq args h; cases args <;> exact StepResult.noConfusion h
      exact key _ rfl args h
    | external r ex hx => exact StepResult.noConfusion h
  | _ => exact StepResult.noConfusion h

theorem retI_cons_not_final (prog : Bodies S S.fns) {A B T : CoreTy} (v : CoreVal A) (fr : Frame S A B)
    (rest : Cont S B T) (o : Final S T) : retI prog v (.cons fr rest) ≠ .final o := by
  intro h
  cases fr with
  | ifF env th el => cases v; exact StepResult.noConfusion h
  | fstF => cases v; exact StepResult.noConfusion h
  | sndF => cases v; exact StepResult.noConfusion h
  | matchF env bs => cases v; exact StepResult.noConfusion h
  | recF fs pre post key heq env done more => cases more <;> exact StepResult.noConfusion h
  | fieldF i key hi => cases v; exact StepResult.noConfusion h
  | consT hd => cases v; exact StepResult.noConfusion h
  | foldL env init body => cases v; exact StepResult.noConfusion h
  | foldI env xs body => cases xs <;> exact StepResult.noConfusion h
  | fixL env s stop step =>
    cases v with
    | i64V n hn =>
      dsimp only [retI] at h
      split at h
      · unfold raiseUnit at h
        split at h
        · exact StepResult.noConfusion h
        · split at h <;> exact StepResult.noConfusion h
      · exact StepResult.noConfusion h
  | fixS env s left count hb stop step =>
    cases v with
    | boolV c =>
      dsimp only [retI] at h
      split at h
      · exact StepResult.noConfusion h
      · split at h <;> exact StepResult.noConfusion h
  | primArgsF op pre post heq env done more =>
    cases more with
    | nil =>
      dsimp only [retI] at h
      split at h
      · exact StepResult.noConfusion h
      · unfold raiseUnit at h
        split at h
        · exact StepResult.noConfusion h
        · split at h <;> exact StepResult.noConfusion h
    | cons x more' => exact StepResult.noConfusion h
  | callArgsF i f hf pre post heq env done more => cases more <;> exact StepResult.noConfusion h
  | _ => exact StepResult.noConfusion h

theorem raiseI_cons_not_final {A B T P : CoreTy} (r : RaisedRef) (hr : catalogPt S.catalog r = some P)
    (v : CoreVal P) (fr : Frame S A B) (rest : Cont S B T) (o : Final S T) :
    raiseI r hr v (.cons fr rest) ≠ .final o := by
  intro h
  cases fr with
  | handleF r' h' env hd =>
    unfold raiseI at h
    dsimp only at h
    split at h <;> exact StepResult.noConfusion h
  | _ => exact StepResult.noConfusion h

/-- Simulation (first-order analogue of 06 §19 final-outcome correspondence), one step: a typed final outcome is
    the raw machine's final outcome of the erased configuration. -/
theorem final_sim (p : RawProg) (prog : Bodies S S.fns) {T : CoreTy} (c : Config S T) (o : Final S T)
    (h : stepI prog c = .final o) : Raw.step p c.erase = finalOut o :=
  match c, h with
  | ⟨_, .evalC env e, k⟩, h => absurd h (evalI_not_final prog env e k o)
  | ⟨_, .retC v, .nil⟩, h => by
      have e := StepResult.final.inj h; subst e; rfl
  | ⟨_, .retC v, .cons fr rest⟩, h => absurd h (retI_cons_not_final prog v fr rest o)
  | ⟨_, .raiseC r hr v, .nil⟩, h => by
      have e := StepResult.final.inj h; subst e; rfl
  | ⟨_, .raiseC r hr v, .cons fr rest⟩, h => absurd h (raiseI_cons_not_final r hr v fr rest o)

/-- 06 §15 `scmStep(c) = final o ↔ c is a final configuration for o`. -/
theorem stepI_final_iff (prog : Bodies S S.fns) {T : CoreTy} (c : Config S T) (o : Final S T) :
    stepI prog c = .final o ↔ IsFinalConfig c o := by
  constructor
  · intro h
    match c, h with
    | ⟨_, .evalC env e, k⟩, h => exact absurd h (evalI_not_final prog env e k o)
    | ⟨_, .retC v, .nil⟩, h => exact (StepResult.final.inj h).symm
    | ⟨_, .retC v, .cons fr rest⟩, h => exact absurd h (retI_cons_not_final prog v fr rest o)
    | ⟨_, .raiseC r hr v, .nil⟩, h => exact (StepResult.final.inj h).symm
    | ⟨_, .raiseC r hr v, .cons fr rest⟩, h => exact absurd h (raiseI_cons_not_final r hr v fr rest o)
  · intro h
    obtain ⟨A, ctl, k⟩ := c
    cases ctl with
    | evalC env e => exact h.elim
    | retC v =>
      cases k with
      | nil => have e : o = .returned v := h; rw [e]; rfl
      | cons fr rest => exact h.elim
    | raiseC r hr v =>
      cases k with
      | nil => have e : o = .raised r hr v := h; rw [e]; rfl
      | cons fr rest => exact h.elim

/-- 06 §16 preservation: a raw configuration that a typed one erases to steps
    (in a well-formed program) only to the erasure of a typed configuration. -/
theorem preservation (p : RawProg) (prog : Bodies S S.fns) (hp : Bodies.erasures prog = p.fns.map RawFnDef.body)
    {T : CoreTy} (r r' : Raw.Config) (c : Config S T)
    (hc : c.erase = r) (hne : c.WF) (hs : Raw.step p r = Raw.next r') :
    RawRel.RawConfigAt S T r' := by
  subst hc
  cases Progress.progress prog c hne with
  | inl hn =>
    obtain ⟨c', hc'⟩ := hn
    cases step_sim p prog hp c c' hc' with
    | inl he =>
      rw [he] at hs
      have e : c'.erase = r' := by
        have := congrArg Raw.Out.config hs
        exact this
      exact ⟨c', e⟩
    | inr hst =>
      rw [hst] at hs
      have h' : (0 : Int) = 1 := congrArg Raw.Out.ok hs
      exact absurd h' (by decide)
  | inr hf =>
    obtain ⟨o, ho⟩ := hf
    rw [final_sim p prog c o ho] at hs
    cases o with
    | returned v =>
      have h' : (1 : Int) = 0 := congrArg Raw.Out.kind hs
      exact absurd h' (by decide)
    | raised rr _ v =>
      have h' : (2 : Int) = 0 := congrArg Raw.Out.kind hs
      exact absurd h' (by decide)

/-! ## Instance witnesses (M-005) -/

namespace Witness
open Rcic.Scm.NoStuck.Witness
def P1 : RawProg := ⟨[], [], cat, 0⟩
def c1 : Config S1 .i64 := ⟨.i64, .retC NoStuck.Witness.five, .nil⟩
example : Raw.step P1 c0.erase = Raw.next c1.erase ∨ Raw.step P1 c0.erase = Raw.stuck :=
  step_sim (S := S1) P1 .nil rfl c0 c1 rfl
example : Raw.step P1 c1.erase = finalOut (S := S1) (T := .i64) (.returned NoStuck.Witness.five) :=
  final_sim (S := S1) P1 .nil c1 (.returned NoStuck.Witness.five) rfl
example : IsFinalConfig c1 (.returned NoStuck.Witness.five) :=
  (stepI_final_iff (S := S1) .nil c1 (.returned NoStuck.Witness.five)).mp rfl
example : RawRel.RawConfigAt S1 .i64 c1.erase :=
  preservation (S := S1) P1 .nil rfl c0.erase c1.erase c0 rfl ⟨trivial, trivial⟩ rfl
end Witness

end Rcic.Scm.Sim
