/-
RCIC 06 §16 — residue-row safety (#6029 K3, segment 7).

Owner text: 06 §16 "residue-row safety: every raised ref is in the derived
entry row". 06 §7: rows are "derived as the least fixed point over: direct
raises, primitive rows, external call rows, local recursive call equations,
handler removal".

The row equations are stated here over typed expressions, scoped exactly:
`CoreExpr.Row ρ e r` — `e` may raise `r`, given a row assignment `ρ` for the
local functions. A `raise r` contributes `r`; a primitive its direct row
(`primRow`, 06 §11 with E-06LenRows); a bounded fix `negative_loop_bound`; a
local call `ρ i`; a handler for `r'` removes `r'` from its BODY only (its
handler expression's row is kept; E-06HandlerScope, 00 §19.7). A row
assignment is admissible when it is a prefixpoint of the equations over every
body (`RowPrefix`); the least fixed point of 06 §7 is one, so the theorem
covers it. `ScmRowDerive` computes that least fixed point (`deriveRows`,
pinned to `apps/rcic-scm-rows`) and proves it is the least prefixpoint.

06 §7's "external call rows" are NOT TRANSCRIBED (#6029 K3 HOLD item 3): in
this bundle an external call has no body and the machine refuses it as an
integrity residue (`Bridge.external_call_refused`), so it never raises; its
`CoreExpr.Row` is its arguments' row only. When the bundle contains the other
groups (06 §7 transitive closure), an external call contributes the callee
group's entry row and the clause is transcribed then.

`residue_row_safety`: an execution from an entry body, in an admissible row
assignment, that ends in a final raised outcome raises a ref in the entry's
row.

`apps/rcic-residue-rows` (stand-in, its APP.md records the defect): its
handler removal subtracts a handled ref from a function's WHOLE row
(`rcic.residue_rows_pass_one` = `minus (union direct ext) handled`), not from
the handler's scope; a ref raised outside the handler is then dropped. Those
rows are not in general prefixpoints of the scoped equations here
(E-06HandlerScope). The scoped derivation over core programs is
`apps/rcic-scm-rows`, transcribed in `ScmRowDerive`.
-/
import rcic.ScmSim

namespace Rcic.Scm

section Rows
variable {S : Sig} (ρ : Nat → RaisedRef → Prop) (ρx : String → RaisedRef → Prop)

mutual
def CoreExpr.Row : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → RaisedRef → Prop
  | _, _, .lit _, _ => False
  | _, _, .var _ _, _ => False
  | _, _, .letE a b, r => a.Row r ∨ b.Row r
  | _, _, .ifE c th el, r => c.Row r ∨ th.Row r ∨ el.Row r
  | _, _, .pairE a b, r => a.Row r ∨ b.Row r
  | _, _, .fstE a, r => a.Row r
  | _, _, .sndE a, r => a.Row r
  | _, _, .injE _ _ _ a, r => a.Row r
  | _, _, .matchSum s bs _, r => s.Row r ∨ bs.Row r
  | _, _, .recordE xs _, r => xs.Row r
  | _, _, .fieldE _ _ _ e, r => e.Row r
  | _, _, .nilE, _ => False
  | _, _, .consE h tl, r => h.Row r ∨ tl.Row r
  | _, _, .foldList l init body, r => l.Row r ∨ init.Row r ∨ body.Row r
  | _, _, .boundedFix init limit stop step, r =>
      init.Row r ∨ limit.Row r ∨ stop.Row r ∨ step.Row r ∨ r = "negative_loop_bound"
  | _, _, .prim op args, r => r ∈ primRow op ∨ args.Row r
  | _, _, .call (.local i _ _) args, r => ρ i r ∨ args.Row r
  | _, _, .call (.external n _ _) args, r => args.Row r ∨ ρx n r
  | _, _, .raise r' _ p, r => r = r' ∨ p.Row r
  | _, _, .handle r' _ body hd, r => (body.Row r ∧ r ≠ r') ∨ hd.Row r
def Branches.Row : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → RaisedRef → Prop
  | _, _, _, .nil, _ => False
  | _, _, _, .cons b bs, r => b.Row r ∨ bs.Row r
def Fields.Row : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → RaisedRef → Prop
  | _, _, .nil, _ => False
  | _, _, .cons _ x xs, r => x.Row r ∨ xs.Row r
def Args.Row : {Γ ps : List CoreTy} → Args S Γ ps → RaisedRef → Prop
  | _, _, .nil, _ => False
  | _, _, .cons x xs, r => x.Row r ∨ xs.Row r
end

def Frame.Row {A B : CoreTy} : Frame S A B → RaisedRef → Prop
  | .letF _ b, r => b.Row ρ ρx r
  | .ifF _ th el, r => th.Row ρ ρx r ∨ el.Row ρ ρx r
  | .pairL _ b, r => b.Row ρ ρx r
  | .pairR _, _ => False
  | .fstF, _ => False
  | .sndF, _ => False
  | .injF _ _, _ => False
  | .matchF _ bs, r => bs.Row ρ ρx r
  | .recF _ _ _ _ _ _ _ rest, r => rest.Row ρ ρx r
  | .fieldF _ _ _, _ => False
  | .consH _ tl, r => tl.Row ρ ρx r
  | .consT _, _ => False
  | .foldL _ init body, r => init.Row ρ ρx r ∨ body.Row ρ ρx r
  | .foldI _ _ body, r => body.Row ρ ρx r
  | .fixI _ limit stop step, r => limit.Row ρ ρx r ∨ stop.Row ρ ρx r ∨ step.Row ρ ρx r ∨ r = "negative_loop_bound"
  | .fixL _ _ stop step, r => stop.Row ρ ρx r ∨ step.Row ρ ρx r ∨ r = "negative_loop_bound"
  | .fixS _ _ _ _ _ stop step, r => stop.Row ρ ρx r ∨ step.Row ρ ρx r
  | .fixT _ _ _ _ stop step, r => stop.Row ρ ρx r ∨ step.Row ρ ρx r
  | .primArgsF op _ _ _ _ _ rest, r => r ∈ primRow op ∨ rest.Row ρ ρx r
  | .callArgsF i _ _ _ _ _ _ _ rest, r => ρ i r ∨ rest.Row ρ ρx r
  | .retF, _ => False
  | .handleF _ _ _ hd, r => hd.Row ρ ρx r
  | .raiseF r' _, r => r = r'

/-- `r`, raised at the top of `k`, escapes `k` into `target`, or is caught. -/
def Cont.Esc (target : RaisedRef → Prop) {A T : CoreTy} : Cont S A T → RaisedRef → Prop
  | .nil, r => target r
  | .cons (.handleF r' _ _ _) k, r => r = r' ∨ k.Esc target r
  | .cons _ k, r => k.Esc target r

/-- Every frame's pending code raises only refs that escape the rest. -/
def Cont.Safe (target : RaisedRef → Prop) {A T : CoreTy} : Cont S A T → Prop
  | .nil => True
  | .cons fr k => (∀ r, fr.Row ρ ρx r → k.Esc target r) ∧ k.Safe target

def Control.Row {A : CoreTy} : Control S A → RaisedRef → Prop
  | .evalC _ e, r => e.Row ρ ρx r
  | .retC _, _ => False
  | .raiseC r' _ _, r => r = r'

def Config.RowSafe (target : RaisedRef → Prop) {T : CoreTy} (c : Config S T) : Prop :=
  (∀ r, c.ctl.Row ρ ρx r → c.k.Esc target r) ∧ c.k.Safe ρ ρx target

/-- The row assignment is a prefixpoint of the equations over every body. -/
def RowPrefix (prog : Bodies S S.fns) : Prop :=
  ∀ (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f) (r : RaisedRef), (prog.at i f hf).Row ρ ρx r → ρ i r

end Rows

end Rcic.Scm

namespace Rcic.Scm.RowSafety
open Rcic.Scm Rcic.Scm.Progress

variable {S : Sig} (ρ : Nat → RaisedRef → Prop) (ρx : String → RaisedRef → Prop) (prog : Bodies S S.fns) (target : RaisedRef → Prop)

theorem branches_at_row {Γ : List CoreTy} {T : CoreTy} :
    ∀ {ts : List CoreTy} {A : CoreTy} (bs : Branches S Γ ts T) (i : Nat) (h : ts.get? i = some A) (r : RaisedRef),
    (bs.at i h).Row ρ ρx r → bs.Row ρ ρx r
  | _ :: _, _, .cons b _, 0, h, r, hr => by
      have e := Option.some.inj h; subst e
      exact Or.inl hr
  | _ :: _, _, .cons _ bs, n + 1, h, r, hr => Or.inr (branches_at_row bs n h r hr)
  | [], _, .nil, _, h, _, _ => nomatch h

theorem raiseUnit_rowSafe {B T : CoreTy} (r0 : RaisedRef) (rest : Cont S B T) (c' : Config S T)
    (hesc : rest.Esc target r0) (hk : rest.Safe ρ ρx target) (h : raiseUnit r0 rest = .next c') :
    c'.RowSafe ρ ρx target := by
  unfold raiseUnit at h
  split at h
  · exact StepResult.noConfusion h
  · split at h
    · have e := StepResult.next.inj h; subst e
      exact ⟨fun r hr => by rw [hr]; exact hesc, hk⟩
    · exact StepResult.noConfusion h

theorem evalI_rowSafe (hpre : RowPrefix ρ ρx prog) {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) :
    ∀ {A : CoreTy} (e : CoreExpr S Γ A) (k : Cont S A T) (c' : Config S T),
    (∀ r, e.Row ρ ρx r → k.Esc target r) → k.Safe ρ ρx target → evalI prog env e k = .next c' →
    c'.RowSafe ρ ρx target := by
  intro A e k c' he hk h
  cases e with
  | lit v => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hk⟩
  | var i hi => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hk⟩
  | letE a b =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | ifE c th el =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | pairE a b =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | fstE a => have e := StepResult.next.inj h; subst e; exact ⟨he, fun _ hr => hr.elim, hk⟩
  | sndE a => have e := StepResult.next.inj h; subst e; exact ⟨he, fun _ hr => hr.elim, hk⟩
  | injE ts i hi a => have e := StepResult.next.inj h; subst e; exact ⟨he, fun _ hr => hr.elim, hk⟩
  | matchSum s bs hne =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | recordE xs hkeys =>
    cases xs with
    | nil => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hk⟩
    | cons key x rest =>
      have e := StepResult.next.inj h; subst e
      exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | fieldE i key hi r0 => have e := StepResult.next.inj h; subst e; exact ⟨he, fun _ hr => hr.elim, hk⟩
  | nilE => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hk⟩
  | consE hd tl =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | foldList l init body =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | boundedFix init limit stop step =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inl hr), fun r hr => he r (Or.inr hr), hk⟩
  | prim op args =>
    have key : ∀ (ps : List CoreTy) (heq : (primSig op).ps = ps) (args : Args S Γ ps),
        (∀ r, (r ∈ primRow op ∨ args.Row ρ ρx r) → k.Esc target r) →
        pushPrim op env ps heq args k = .next c' → c'.RowSafe ρ ρx target := by
      intro ps heq args ha h
      cases args with
      | nil => exact StepResult.noConfusion h
      | cons x rest =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => ha r (Or.inr (Or.inl hr)),
          fun r hr => hr.elim (fun h1 => ha r (Or.inl h1)) (fun h2 => ha r (Or.inr (Or.inr h2))), hk⟩
    exact key _ rfl args he h
  | call f args =>
    cases f with
    | «local» i fs hf =>
      have key : ∀ (ps : List CoreTy) (heq : fs.params = ps) (args : Args S Γ ps),
          (∀ r, (ρ i r ∨ args.Row ρ ρx r) → k.Esc target r) →
          pushCall prog i fs hf env ps heq args k = .next c' → c'.RowSafe ρ ρx target := by
        intro ps heq args ha h
        cases args with
        | nil =>
          have e := StepResult.next.inj h; subst e
          exact ⟨fun r hr => ha r (Or.inl (hpre i fs hf r hr)), fun _ hr => hr.elim, hk⟩
        | cons x rest =>
          have e := StepResult.next.inj h; subst e
          exact ⟨fun r hr => ha r (Or.inr (Or.inl hr)),
            fun r hr => hr.elim (fun h1 => ha r (Or.inl h1)) (fun h2 => ha r (Or.inr (Or.inr h2))), hk⟩
      exact key _ rfl args he h
    | external r ex hx => exact StepResult.noConfusion h
  | raise r' hr' p =>
    have e := StepResult.next.inj h; subst e
    exact ⟨fun r hr => he r (Or.inr hr), fun r hr => he r (Or.inl hr), hk⟩
  | handle r' hr' body hd =>
    have e := StepResult.next.inj h; subst e
    refine ⟨fun r hr => ?_, fun r hr => he r (Or.inr hr), hk⟩
    exact if hrr : r = r' then Or.inl hrr else Or.inr (he r (Or.inl ⟨hr, hrr⟩))

theorem raiseI_rowSafe {A T P : CoreTy} (r0 : RaisedRef) (hr0 : catalogPt S.catalog r0 = some P) (v : CoreVal P) :
    ∀ (k : Cont S A T) (c' : Config S T), k.Esc target r0 → k.Safe ρ ρx target →
    raiseI r0 hr0 v k = .next c' → c'.RowSafe ρ ρx target := by
  intro k c' hesc hk h
  cases k with
  | nil => exact StepResult.noConfusion h
  | cons fr rest =>
    cases fr with
    | handleF r' h' env hd =>
      unfold raiseI at h
      dsimp only at h
      split at h
      · have e := StepResult.next.inj h; subst e
        exact ⟨hk.1, hk.2⟩
      · rename_i hne
        have e := StepResult.next.inj h; subst e
        refine ⟨fun r hr => ?_, hk.2⟩
        rw [hr]
        exact hesc.elim (fun h1 => absurd h1.symm hne) id
    | _ =>
      have e := StepResult.next.inj h; subst e
      exact ⟨fun r hr => by rw [hr]; exact hesc, hk.2⟩

theorem retI_rowSafe (hpre : RowPrefix ρ ρx prog) {T : CoreTy} :
    ∀ {A : CoreTy} (v : CoreVal A) (k : Cont S A T) (c' : Config S T),
    k.Safe ρ ρx target → retI prog v k = .next c' → c'.RowSafe ρ ρx target := by
  intro A v k c' hk h
  cases k with
  | nil => exact StepResult.noConfusion h
  | cons fr rest =>
    obtain ⟨hfr, hrest⟩ := hk
    cases fr with
    | letF env b => have e := StepResult.next.inj h; subst e; exact ⟨hfr, hrest⟩
    | ifF env th el =>
      cases v with
      | boolV c =>
        cases c
        · have e := StepResult.next.inj h; subst e; exact ⟨fun r hr => hfr r (Or.inr hr), hrest⟩
        · have e := StepResult.next.inj h; subst e; exact ⟨fun r hr => hfr r (Or.inl hr), hrest⟩
    | pairL env b =>
      have e := StepResult.next.inj h; subst e; exact ⟨hfr, fun _ hr => hr.elim, hrest⟩
    | pairR a => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | fstF => cases v; have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | sndF => cases v; have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | injF i hi => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | matchF env bs =>
      cases v with
      | injV i A' hi w =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => hfr r (branches_at_row ρ ρx bs i hi r hr), hrest⟩
    | recF fs pre post key heq env done more =>
      cases more with
      | nil => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
      | cons key2 x more' =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => hfr r (Or.inl hr), fun r hr => hfr r (Or.inr hr), hrest⟩
    | fieldF i key hi => cases v; have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | consH env tl =>
      have e := StepResult.next.inj h; subst e; exact ⟨hfr, fun _ hr => hr.elim, hrest⟩
    | consT hd => cases v; have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | foldL env init body =>
      cases v with
      | listV xs =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => hfr r (Or.inl hr), fun r hr => hfr r (Or.inr hr), hrest⟩
    | foldI env xs body =>
      cases xs with
      | nil => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
      | cons x xs' => have e := StepResult.next.inj h; subst e; exact ⟨hfr, hfr, hrest⟩
    | fixI env limit stop step =>
      have e := StepResult.next.inj h; subst e
      exact ⟨fun r hr => hfr r (Or.inl hr), fun r hr => hfr r (Or.inr hr), hrest⟩
    | fixL env s stop step =>
      cases v with
      | i64V n hn =>
        dsimp only [retI] at h
        split at h
        · exact raiseUnit_rowSafe ρ ρx target "negative_loop_bound" rest c'
            (hfr _ (Or.inr (Or.inr rfl))) hrest h
        · have e := StepResult.next.inj h; subst e
          exact ⟨fun r hr => hfr r (Or.inl hr),
            fun r hr => hfr r (hr.elim (fun a => Or.inl a) (fun b => Or.inr (Or.inl b))), hrest⟩
    | fixS env s left count hb stop step =>
      cases v with
      | boolV c =>
        dsimp only [retI] at h
        split at h
        · have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
        · split at h
          · have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
          · have e := StepResult.next.inj h; subst e
            exact ⟨fun r hr => hfr r (Or.inr hr), hfr, hrest⟩
    | fixT env left count hb stop step =>
      have e := StepResult.next.inj h; subst e
      exact ⟨fun r hr => hfr r (Or.inl hr), hfr, hrest⟩
    | primArgsF op pre post heq env done more =>
      cases more with
      | nil =>
        dsimp only [retI] at h
        split at h
        · have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
        · rename_i r0 hlaw
          exact raiseUnit_rowSafe ρ ρx target r0 rest c'
            (hfr r0 (Or.inl (primLaw_raised_mem op _ r0 hlaw))) hrest h
      | cons x more' =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => hfr r (Or.inr (Or.inl hr)),
          fun r hr => hr.elim (fun h1 => hfr r (Or.inl h1)) (fun h2 => hfr r (Or.inr (Or.inr h2))), hrest⟩
    | callArgsF i f hf pre post heq env done more =>
      cases more with
      | nil =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => hfr r (Or.inl (hpre i f hf r hr)), fun _ hr => hr.elim, hrest⟩
      | cons x more' =>
        have e := StepResult.next.inj h; subst e
        exact ⟨fun r hr => hfr r (Or.inr (Or.inl hr)),
          fun r hr => hr.elim (fun h1 => hfr r (Or.inl h1)) (fun h2 => hfr r (Or.inr (Or.inr h2))), hrest⟩
    | retF => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | handleF r' hr' env hd => have e := StepResult.next.inj h; subst e; exact ⟨fun _ hr => hr.elim, hrest⟩
    | raiseF r' hr' =>
      have e := StepResult.next.inj h; subst e
      exact ⟨fun r hr => hfr r hr, hrest⟩

theorem stepI_rowSafe (hpre : RowPrefix ρ ρx prog) {T : CoreTy} (c c' : Config S T)
    (hc : c.RowSafe ρ ρx target) (h : stepI prog c = .next c') : c'.RowSafe ρ ρx target :=
  match c, hc, h with
  | ⟨_, .evalC env e, k⟩, hc, h => evalI_rowSafe ρ ρx prog target hpre env e k c' hc.1 hc.2 h
  | ⟨_, .retC v, k⟩, hc, h => retI_rowSafe ρ ρx prog target hpre v k c' hc.2 h
  | ⟨_, .raiseC r hr v, k⟩, hc, h => raiseI_rowSafe ρ ρx target r hr v k c' (hc.1 r rfl) hc.2 h

theorem runs_rowSafe (hpre : RowPrefix ρ ρx prog) {T : CoreTy} :
    ∀ {n : Nat} {c c' : Config S T}, SCMRuns prog n c c' → c.RowSafe ρ ρx target → c'.RowSafe ρ ρx target
  | _, _, _, .refl _, hc => hc
  | _, _, _, .step hs hr, hc => runs_rowSafe hpre hr (stepI_rowSafe ρ ρx prog target hpre _ _ hc hs)

/-- 06 §16 residue-row safety: a run from an entry body in an admissible row
    assignment that ends in a final raised outcome raises a ref in the
    entry's row. -/
theorem residue_row_safety (hpre : RowPrefix ρ ρx prog) (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f)
    (args : CoreVals f.params) {n : Nat} {cf : Config S f.result}
    (hr : SCMRuns prog n ⟨f.result, .evalC args (prog.at i f hf), .nil⟩ cf)
    {r : RaisedRef} {P : CoreTy} {hP : catalogPt S.catalog r = some P} {v : CoreVal P}
    (hfin : stepI prog cf = .final (.raised r hP v)) : ρ i r := by
  have h0 : Config.RowSafe ρ ρx (ρ i) ⟨f.result, .evalC args (prog.at i f hf), .nil⟩ :=
    ⟨fun r hr => hpre i f hf r hr, trivial⟩
  have hs := runs_rowSafe ρ ρx prog (ρ i) hpre hr h0
  revert hfin hs
  obtain ⟨A, ctl, k⟩ := cf
  cases ctl with
  | evalC env e => intro hfin _; exact absurd hfin (Sim.evalI_not_final prog env e k _)
  | retC v' =>
    cases k with
    | nil => intro hfin _; exact Final.noConfusion (StepResult.final.inj hfin)
    | cons fr rest => intro hfin _; exact absurd hfin (Sim.retI_cons_not_final prog v' fr rest _)
  | raiseC r' hr' v' =>
    cases k with
    | nil =>
      intro hfin hs
      have e := StepResult.final.inj hfin
      injection e with hP' hrr
      rw [← hrr]
      exact hs.1 r' rfl
    | cons fr rest => intro hfin _; exact absurd hfin (Sim.raiseI_cons_not_final r' hr' v' fr rest _)

/-! ## Instance witness (M-005): an admissible row assignment and a run that
    ends raised. -/

namespace Witness
def S2 : Sig := ⟨[⟨[], unitTy⟩], [], [⟨"bad_input", unitTy⟩]⟩
def body : CoreExpr S2 [] unitTy := .raise "bad_input" rfl (.lit unitV)
def prog2 : Bodies S2 S2.fns := .cons body .nil
def ρ2 : Nat → RaisedRef → Prop := fun _ r => r = "bad_input"
def ρx2 : String → RaisedRef → Prop := fun _ _ => False

theorem prefix2 : RowPrefix ρ2 ρx2 prog2 := by
  intro i f hf r hr
  cases i with
  | zero =>
    have e : f = ⟨[], unitTy⟩ := (Option.some.inj hf).symm
    subst e
    exact hr.elim id (fun h => h.elim)
  | succ n => exact Option.noConfusion hf

def c0 : Config S2 unitTy := ⟨unitTy, .evalC .nil (prog2.at 0 ⟨[], unitTy⟩ rfl), .nil⟩
def c1 : Config S2 unitTy := ⟨unitTy, .evalC .nil (.lit unitV), .cons (.raiseF "bad_input" rfl) .nil⟩
def c2 : Config S2 unitTy := ⟨unitTy, .retC unitV, .cons (.raiseF "bad_input" rfl) .nil⟩
def c3 : Config S2 unitTy := ⟨unitTy, .raiseC "bad_input" rfl unitV, .nil⟩

example : ρ2 0 "bad_input" :=
  residue_row_safety ρ2 ρx2 prog2 prefix2 0 ⟨[], unitTy⟩ rfl .nil
    (n := 3) (cf := c3) (.step (c' := c1) rfl (.step (c' := c2) rfl (.step (c' := c3) rfl (.refl c3))))
    (hP := rfl) (v := unitV) rfl
end Witness

end Rcic.Scm.RowSafety
