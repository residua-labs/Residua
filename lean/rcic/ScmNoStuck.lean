/-
RCIC 06 §16 — no stuck: well-formed executions are final or step
(#6029 K3, segment 3).

Owner text (06 §16): "no stuck: well-formed executions are final or step".
"Well-formed" is `ScmProgress`'s `WF`, over the whole configuration and the
program: no external call anywhere in the configuration (control and every
frame) or in any function body, and every primitive / bounded fix that occurs
there has its residues catalogued with the unit payload. The invariant is
preserved by every step (`stepI_wf`), so every configuration an execution
reaches steps or is final (`no_stuck`).
-/
import rcic.ScmProgress

namespace Rcic.Scm.NoStuck
open Rcic.Scm Rcic.Scm.Progress

variable {S : Sig} (prog : Bodies S S.fns)

theorem branches_at_wf {Γ : List CoreTy} {T : CoreTy} :
    ∀ {ts : List CoreTy} {A : CoreTy} (bs : Branches S Γ ts T) (i : Nat) (h : ts.get? i = some A),
    bs.WF → (bs.at i h).WF
  | _ :: _, _, .cons b _, 0, h, hb => by
      have e := Option.some.inj h
      subst e
      exact hb.1
  | _ :: _, _, .cons _ bs, n + 1, h, hb => branches_at_wf bs n h hb.2
  | [], _, .nil, _, h, _ => nomatch h

theorem bodies_at_wf : ∀ {fs : List FnSig} (bs : Bodies S fs) (i : Nat) (f : FnSig)
    (h : fs.get? i = some f), bs.WF → (bs.at i f h).WF
  | _ :: _, .cons b _, 0, _, h, hb => by
      have e := Option.some.inj h
      subst e
      exact hb.1
  | _ :: _, .cons _ bs, n + 1, f, h, hb => bodies_at_wf bs n f h hb.2
  | [], .nil, _, _, h, _ => nomatch h

theorem raiseUnit_wf {B T : CoreTy} (r : RaisedRef) (rest : Cont S B T) (c' : Config S T)
    (hk : rest.WF) (h : raiseUnit r rest = .next c') : c'.WF := by
  unfold raiseUnit at h
  split at h
  · exact StepResult.noConfusion h
  · split at h
    · have e := StepResult.next.inj h
      subst e
      exact ⟨trivial, hk⟩
    · exact StepResult.noConfusion h

theorem evalI_wf (hp : prog.WF) {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) :
    ∀ {A : CoreTy} (e : CoreExpr S Γ A) (k : Cont S A T) (c' : Config S T),
    e.WF → k.WF → evalI prog env e k = .next c' → c'.WF := by
  intro A e k c' he hk h
  cases e with
  | lit v => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk⟩
  | var i hi => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk⟩
  | letE a b => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | ifE c th el => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | pairE a b => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | fstE a => have e := StepResult.next.inj h; subst e; exact ⟨he, trivial, hk⟩
  | sndE a => have e := StepResult.next.inj h; subst e; exact ⟨he, trivial, hk⟩
  | injE ts i hi a => have e := StepResult.next.inj h; subst e; exact ⟨he, trivial, hk⟩
  | matchSum s bs hne => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | recordE xs hkeys =>
    cases xs with
    | nil => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk⟩
    | cons key x rest => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | fieldE i key hi r => have e := StepResult.next.inj h; subst e; exact ⟨he, trivial, hk⟩
  | nilE => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk⟩
  | consE hd tl => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | foldList l init body => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩
  | boundedFix init limit stop step =>
    have e := StepResult.next.inj h; subst e; exact ⟨he.2.1, ⟨he.1, he.2.2⟩, hk⟩
  | prim op args =>
    have key : ∀ (ps : List CoreTy) (heq : (primSig op).ps = ps) (args : Args S Γ ps),
        args.WF → pushPrim op env ps heq args k = .next c' → c'.WF := by
      intro ps heq args ha h
      cases args with
      | nil => exact StepResult.noConfusion h
      | cons x rest => have e := StepResult.next.inj h; subst e; exact ⟨ha.1, ⟨he.1, ha.2⟩, hk⟩
    exact key _ rfl args he.2 h
  | call f args =>
    cases f with
    | «local» i fs hf =>
      have key : ∀ (ps : List CoreTy) (heq : fs.params = ps) (args : Args S Γ ps),
          args.WF → pushCall prog i fs hf env ps heq args k = .next c' → c'.WF := by
        intro ps heq args ha h
        cases args with
        | nil =>
          have e := StepResult.next.inj h; subst e
          exact ⟨bodies_at_wf prog i fs hf hp, trivial, hk⟩
        | cons x rest => have e := StepResult.next.inj h; subst e; exact ⟨ha.1, ha.2, hk⟩
      exact key _ rfl args he h
    | external r ex hx => exact he.elim
  | raise r hr p => have e := StepResult.next.inj h; subst e; exact ⟨he, trivial, hk⟩
  | handle r hr body hd => have e := StepResult.next.inj h; subst e; exact ⟨he.1, he.2, hk⟩

theorem raiseI_wf {A T P : CoreTy} (r : RaisedRef) (hr : catalogPt S.catalog r = some P) (v : CoreVal P) :
    ∀ (k : Cont S A T) (c' : Config S T), k.WF → raiseI r hr v k = .next c' → c'.WF := by
  intro k c' hk h
  cases k with
  | nil => exact StepResult.noConfusion h
  | cons fr rest =>
    cases fr with
    | handleF r' h' env hd =>
      unfold raiseI at h
      dsimp only at h
      split at h
      · have e := StepResult.next.inj h; subst e; exact ⟨hk.1, hk.2⟩
      · have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | _ => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩

theorem retI_wf (hp : prog.WF) {T : CoreTy} :
    ∀ {A : CoreTy} (v : CoreVal A) (k : Cont S A T) (c' : Config S T),
    k.WF → retI prog v k = .next c' → c'.WF := by
  intro A v k c' hk h
  cases k with
  | nil => exact StepResult.noConfusion h
  | cons fr rest =>
    cases fr with
    | letF env b => have e := StepResult.next.inj h; subst e; exact ⟨hk.1, hk.2⟩
    | ifF env th el =>
      cases v with
      | boolV c =>
        cases c
        · have e := StepResult.next.inj h; subst e; exact ⟨hk.1.2, hk.2⟩
        · have e := StepResult.next.inj h; subst e; exact ⟨hk.1.1, hk.2⟩
    | pairL env b => have e := StepResult.next.inj h; subst e; exact ⟨hk.1, trivial, hk.2⟩
    | pairR a => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | fstF => cases v; have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | sndF => cases v; have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | injF i hi => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | matchF env bs =>
      cases v with
      | injV i A' hi w =>
        have e := StepResult.next.inj h; subst e
        exact ⟨branches_at_wf bs i hi hk.1, hk.2⟩
    | recF fs pre post key heq env done more =>
      cases more with
      | nil => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
      | cons key2 x more' => have e := StepResult.next.inj h; subst e; exact ⟨hk.1.1, hk.1.2, hk.2⟩
    | fieldF i key hi => cases v; have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | consH env tl => have e := StepResult.next.inj h; subst e; exact ⟨hk.1, trivial, hk.2⟩
    | consT hd => cases v; have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | foldL env init body =>
      cases v with
      | listV xs => have e := StepResult.next.inj h; subst e; exact ⟨hk.1.1, hk.1.2, hk.2⟩
    | foldI env xs body =>
      cases xs with
      | nil => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
      | cons x xs' => have e := StepResult.next.inj h; subst e; exact ⟨hk.1, hk.1, hk.2⟩
    | fixI env limit stop step =>
      have e := StepResult.next.inj h; subst e; exact ⟨hk.1.2.1, ⟨hk.1.1, hk.1.2.2⟩, hk.2⟩
    | fixL env s stop step =>
      cases v with
      | i64V n hn =>
        dsimp only [retI] at h
        split at h
        · exact raiseUnit_wf "negative_loop_bound" rest c' hk.2 h
        · have e := StepResult.next.inj h; subst e; exact ⟨hk.1.2.1, hk.1.2, hk.2⟩
    | fixS env s left count hb stop step =>
      cases v with
      | boolV c =>
        dsimp only [retI] at h
        split at h
        · have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
        · split at h
          · have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
          · have e := StepResult.next.inj h; subst e; exact ⟨hk.1.2, hk.1, hk.2⟩
    | fixT env left count hb stop step =>
      have e := StepResult.next.inj h; subst e; exact ⟨hk.1.1, hk.1, hk.2⟩
    | primArgsF op pre post heq env done more =>
      cases more with
      | nil =>
        dsimp only [retI] at h
        split at h
        · have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
        · rename_i r _
          exact raiseUnit_wf r rest c' hk.2 h
      | cons x more' =>
        have e := StepResult.next.inj h; subst e; exact ⟨hk.1.2.1, ⟨hk.1.1, hk.1.2.2⟩, hk.2⟩
    | callArgsF i f hf pre post heq env done more =>
      cases more with
      | nil =>
        have e := StepResult.next.inj h; subst e
        exact ⟨bodies_at_wf prog i f hf hp, trivial, hk.2⟩
      | cons x more' => have e := StepResult.next.inj h; subst e; exact ⟨hk.1.1, hk.1.2, hk.2⟩
    | retF => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | handleF r hr env hd => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩
    | raiseF r hr => have e := StepResult.next.inj h; subst e; exact ⟨trivial, hk.2⟩

/-- The well-formedness invariant is preserved by every step. -/
theorem stepI_wf (hp : prog.WF) {T : CoreTy} (c c' : Config S T) (hc : c.WF)
    (h : stepI prog c = .next c') : c'.WF :=
  match c, hc, h with
  | ⟨_, .evalC env e, k⟩, hc, h => evalI_wf prog hp env e k c' hc.1 hc.2 h
  | ⟨_, .retC v, k⟩, hc, h => retI_wf prog hp v k c' hc.2 h
  | ⟨_, .raiseC r hr v, k⟩, hc, h => raiseI_wf r hr v k c' hc.2 h

theorem runs_wf (hp : prog.WF) {T : CoreTy} :
    ∀ {n : Nat} {c c' : Config S T}, SCMRuns prog n c c' → c.WF → c'.WF
  | _, _, _, .refl _, hc => hc
  | _, _, _, .step hs hr, hc => runs_wf hp hr (stepI_wf prog hp _ _ hc hs)

/-- 06 §16 no stuck: every configuration a well-formed execution reaches is
    final or steps. -/
theorem no_stuck (hp : prog.WF) {T : CoreTy} {n : Nat}
    {c c' : Config S T} (hr : SCMRuns prog n c c') (hc : c.WF) :
    (∃ c'', stepI prog c' = .next c'') ∨ (∃ o, stepI prog c' = .final o) :=
  progress prog c' (runs_wf prog hp hr hc)

/-! ## Instance witnesses (M-005): the premises are satisfiable and the
    conclusions are instantiated. -/

namespace Witness
def cat : List CatalogEntry :=
  [⟨"byte_out_of_range", unitTy⟩, ⟨"division_by_zero", unitTy⟩, ⟨"empty_separator", unitTy⟩,
   ⟨"index_out_of_range", unitTy⟩, ⟨"malformed_integer", unitTy⟩, ⟨"negative_loop_bound", unitTy⟩,
   ⟨"nonexact_division", unitTy⟩, ⟨"signed_overflow", unitTy⟩]
def S1 : Sig := ⟨[], [], cat⟩

/-- Every primitive's residues are catalogued in `S1` (so any program over
    `S1` satisfies the catalog half of `WF`). -/
theorem S1_prim (op : PrimOp) : PrimCat S1 op := by
  intro r hr
  have key : (primRow op).all (fun r => decide (catalogPt cat r = some unitTy)) = true := by
    cases op <;> decide
  exact of_decide_eq_true (List.all_eq_true.mp key r hr)

def five : CoreVal .i64 := .i64V 5 ⟨by decide, by decide⟩
def c0 : Config S1 .i64 := ⟨.i64, .evalC .nil (.lit five), .nil⟩

example : (∃ c'', stepI (S := S1) .nil c0 = .next c'') ∨ (∃ o, stepI (S := S1) .nil c0 = .final o) :=
  no_stuck (S := S1) .nil trivial (.refl c0) ⟨trivial, trivial⟩

/-- A program with no primitive and no bounded fix is well formed over the
    EMPTY catalog: the catalog premise is per program (#6029 K3 HOLD item 2a). -/
def S0 : Sig := ⟨[], [], []⟩
def d0 : Config S0 .i64 := ⟨.i64, .evalC .nil (.lit five), .nil⟩
example : (∃ c'', stepI (S := S0) .nil d0 = .next c'') ∨ (∃ o, stepI (S := S0) .nil d0 = .final o) :=
  no_stuck (S := S0) .nil trivial (.refl d0) ⟨trivial, trivial⟩
/-- … and a program using `add` needs exactly `signed_overflow` catalogued. -/
example : PrimCat ⟨[], [], [⟨"signed_overflow", unitTy⟩]⟩ .add := by
  intro r hr
  cases hr with
  | head => rfl
  | tail _ h => cases h
end Witness

end Rcic.Scm.NoStuck
