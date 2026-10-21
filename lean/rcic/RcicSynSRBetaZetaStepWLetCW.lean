import rcic.RcicSynSRBetaZetaStepWClosedWf
import rcic.RcicSynWalkLet
import rcic.RcicSynTyAt
import rcic.RcicSynWalk
import rcic.RcicSynMember
import rcic.RcicSynTable

/-!
# The let-slot walker preserves `ClosedWf` — the boundary residue discharged

cc 23:55Z objective (1). `sortRow_of_allBelowScopedW_letCW` carries one
contract, `LetCtxConvP.ClosedWf (letCtxConvP_of_envWfT hW)`; this module
discharges it for the `EnvWfT`-supplied oracle and re-states the boundary
as `sortRow_of_allBelowScopedW_envWfT` with no contract premise.

The proof mirrors the walker, not the walk's output: `ClosedWf` reads only
the eps-evaluated spine (`TyP.conv` reads its base typing; `CvP` payloads
are never read), the transports dissolve into casts, and the induction
threads one side condition — `stepsCW ss`: every `esub`/`lsub` payload
typing in the skeleton is `ClosedWf` — through the pack transformations
(`shiftStep` wraps payloads in `TyP.wk .. 0`, whose `AssumpCut` is `.zero`).
No CL/EUT fact is ported: every recursive appeal is the walker's own
rank-decreasing edge on a structurally smaller derivation.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 skeleton payloads -/

/-- Per-step `ClosedWf` content: only `esub`/`lsub` carry a typing (the
    replacement); the `cctx` payload is a `CvP`, which `ClosedWf` never
    reads. -/
def PStep.stepCW {E : ResolvedEnv} {n : Nat} : PStep E n → Prop
  | .wk _ _ => True
  | .esub _ _ _ _ _ _ _ _ hv => hv.ClosedWf
  | .lsub _ _ _ _ _ _ _ _ hv => hv.ClosedWf
  | .linst _ _ _ _ _ => True
  | .cctx _ _ _ _ _ _ _ => True

/-- Every `esub`/`lsub` payload typing in the skeleton is `ClosedWf`. -/
def stepsCW {E : ResolvedEnv} {n : Nat} (ss : List (PStep E n)) : Prop :=
  ∀ s ∈ ss, s.stepCW

theorem stepsCW_nil {E : ResolvedEnv} {n : Nat} : stepsCW ([] : List (PStep E n)) := by
  intro s hs
  exact absurd hs (by simp)

theorem stepsCW_cons {E : ResolvedEnv} {n : Nat} {s : PStep E n} {ss : List (PStep E n)}
    (hs : s.stepCW) (h : stepsCW ss) : stepsCW (s :: ss) := by
  intro t ht
  cases ht with
  | head => exact hs
  | tail _ hm => exact h t hm

theorem stepsCW_tail {E : ResolvedEnv} {n : Nat} {s : PStep E n} {ss : List (PStep E n)}
    (h : stepsCW (s :: ss)) : stepsCW ss :=
  fun t ht => h t (List.Mem.tail _ ht)

/-- `shiftStep`'s `esub`/`lsub` payload lands under `TyP.wk .. 0`, whose
    `AssumpCut` is `.zero` — payload `ClosedWf` is preserved. -/
theorem stepCW_shiftStep {E : ResolvedEnv} {n : Nat} (dLocal dFinal : LocalDecl)
    (s : PStep E n) (h : s.stepCW) : (shiftStep dLocal dFinal s).stepCW := by
  cases s with
  | wk => trivial
  | esub => exact ⟨.zero _, h⟩
  | lsub => exact ⟨.zero _, h⟩
  | linst => trivial
  | cctx => trivial

/-- `shiftAll` preserves `stepsCW` (the local binder transport changes as
    the walk descends, so it is an induction index). -/
theorem stepsCW_shiftAll {E : ResolvedEnv} {n : Nat} :
    ∀ (dLocal dFinal : LocalDecl) (ss : List (PStep E n)),
      stepsCW ss → stepsCW (shiftAll dLocal dFinal ss)
  | _, _, [], _ => stepsCW_nil
  | dLocal, dFinal, s :: ss, h =>
      stepsCW_cons (stepCW_shiftStep dLocal dFinal s (h s (by simp)))
        (stepsCW_shiftAll (Skel.onDecl s.sk dLocal) dFinal ss
          (fun t ht => h t (List.Mem.tail _ ht)))

/-- The skeleton condition, packed at the `PackL` it is used with — the
    functional-induction motive ranges over the pack, not the skeleton. -/
def PackL.CW {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx}
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ) : Prop :=
  stepsCW ss

theorem PackL.CW_nil {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {Γ : LCtx} (hget : Γ.get? k = some (.letBinding Dom Val))
    (hslotTy : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hslotVal : CvP E n (Γ.drop (k + 1)) Val Val' Dom) :
    (packNilL hget hslotTy hslotVal).CW :=
  stepsCW_nil

theorem PackL.CW_wkCons {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx} {c : Nat} {d : LocalDecl}
    (h : stepsCW ss) (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (insertAt d c Γ)) :
    (packLConsWk c d p).CW :=
  stepsCW_cons trivial h

theorem PackL.CW_esubCons {E : ResolvedEnv} {n k j : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.assumption t))
    (hv : TyP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t)))
    (hvW : hv.ClosedWf) (h : stepsCW ss)
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ)) :
    (packLEsub hget hv p).CW :=
  stepsCW_cons hvW h

theorem PackL.CW_lsubCons {E : ResolvedEnv} {n k j : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.letBinding t v))
    (hv : TyP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t)))
    (hvW : hv.ClosedWf) (h : stepsCW ss)
    (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ)) :
    (packLLsub hget hv p).CW :=
  stepsCW_cons hvW h

theorem PackL.CW_linstCons {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {ss : List (PStep E n)} {Γ : LCtx} (ls : List Level) (a nStep : Nat)
    (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
    (h : stepsCW ss) (p : PackL E n k Dom Val Dom' Val' uSlot nStep ss (instLvlsCtx ls Γ)) :
    (packLLinst ls a nStep hls hlen p).CW :=
  stepsCW_cons trivial h

theorem PackL.CW_cctxCons {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx} {A A' : Expr Nat}
    {u : Level}
    (hc : CvP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      (Skels.app (steps ss) (lift 0 1 A')) (Skels.app (steps ss) (lift 0 1 A)) (.sort u))
    (h : stepsCW ss) (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (.assumption A' :: Γ)) :
    (packLCctx hc p).CW :=
  stepsCW_cons trivial h

theorem PackL.CW_under {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx}
    {dLocal dFinal : LocalDecl} (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (h : stepsCW ss) (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ) :
    (packLUnder p dLocal dFinal hd).CW :=
  stepsCW_shiftAll dLocal dFinal ss h

/-! ## §2 leaf wrappers -/

/-- `ConvChain.apply` wraps in `TyP.conv` nodes, whose `ClosedWf` reads only
    the base typing. -/
theorem closedWf_convChain {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e a c : Expr Nat} :
    ∀ {h : TyP E n Γ e a}, h.ClosedWf → (cc : ConvChain E n Γ a c) →
      (ConvChain.apply h cc).ClosedWf
  | _, hW, .nil => hW
  | h, hW, .cons (b := b) u hc rest =>
      have hW' : (TyP.conv E n Γ e a b u h hc).ClosedWf := hW
      closedWf_convChain hW' rest

/-- `ClosedWf` content of a `BHit`: only the `esub`/`lsub` replacement
    typing; `keep`/`retype` leaves carry none. -/
def BHit.ClosedWf {E : ResolvedEnv} {n : Nat} {pre fin : LCtx} {term ty : Expr Nat} :
    BHit E n pre fin term ty → Prop
  | .keep _ _ _ => True
  | .repl hv => hv.ClosedWf
  | .retype _ _ _ _ _ => True

theorem bhit_closedWf_castTerm {E : ResolvedEnv} {n : Nat} {pre fin : LCtx}
    {term ty term' : Expr Nat} (ht : term' = term)
    {w : BHit E n pre fin term ty} (hW : w.ClosedWf) :
    (BHit.castTerm ht w).ClosedWf := by
  cases w with
  | keep => trivial
  | repl hv => exact closedWf_tyCast _ _ hW
  | retype => trivial

/-- The slot retype is a `conv` whose base typing is a `bvar` leaf. -/
theorem retypeLetBVarSlot_closedWf {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Val Dom' Val' : Expr Nat} {u : Level}
    (h : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u))
    (hget : Γ.get? k = some (.letBinding Dom Val)) :
    (retypeLetBVarSlot (Val' := Val') h hget).ClosedWf := by
  unfold retypeLetBVarSlot
  trivial

/-- `finishBvarL` outputs `ClosedWf` whenever the hit is: every arm is a
    cast around a `bvar` leaf or the slot retype, optionally wrapped in one
    `ConvChain` (`TyP.conv` reads only its base). -/
theorem finishBvarL_closedWf {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level} {term ty : Expr Nat}
    {hget : Γpre.get? k = some (.letBinding Dom Val)}
    {hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot)}
    {hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u)}
    {w : BHit E n Γpre (setLetB k Dom' Val' Γpre) term ty} (hW : w.ClosedWf) :
    (finishBvarL hget hslot hA w).ClosedWf := by
  cases w with
  | repl hv => exact hW
  | keep j hterm hlook =>
      simp only [finishBvarL]
      split
      · exact closedWf_tyCast _ _
          (retypeLetBVarSlot_closedWf (Val' := _) hslot hget)
      · refine closedWf_tyCast _ _ ?_
        trivial
  | retype j B hterm hlook hc =>
      simp only [finishBvarL]
      split
      · exact closedWf_convChain (cc := hc)
          (closedWf_tyCast _ _ (retypeLetBVarSlot_closedWf (Val' := _) hslot hget))
      · refine closedWf_convChain (cc := hc) (closedWf_tyCast _ _ ?_)
        trivial

/-! ## §3 the `bvar` walk -/

/-- `bwalkAtL` outputs a hit whose `ClosedWf` content is exactly the
    skeleton's payload condition: `keep`/`retype` leaves carry none, the
    `esub`/`lsub` replacement leaf reads the head step's payload (cast into
    place), and `cctx` hits wrap repl leaves in `conv` nodes whose `ClosedWf`
    reads the base. Proof shape mirrors the landed `bwalkAtL_ap`. -/
theorem bwalkAtL_closedWf {E : ResolvedEnv} {n : Nat} (k : Nat) (Dom' Val' : Expr Nat) :
    ∀ (ss : List (PStep E n)) (i : Nat) (A : Expr Nat) (Γ : LCtx)
      (h : lookupType Γ i = some A) (hinv : EsInv ss) (hrun : RunL k Dom' Val' ss Γ),
      stepsCW ss → (bwalkAtL k Dom' Val' ss i A Γ h hinv hrun).ClosedWf
  | [], _, _, _, _, _, _, _ => by
      unfold bwalkAtL; trivial
  | .wk c d :: ss, i, A, Γ, h, .wk _ _ hinv, .wk _ _ hrun, hss => by
      unfold bwalkAtL
      split
      · exact bhit_closedWf_castTerm _ (bwalkAtL_closedWf k Dom' Val' ss i _ _ _ hinv hrun (stepsCW_tail hss))
      · exact bhit_closedWf_castTerm _
          (bwalkAtL_closedWf k Dom' Val' ss (i + 1) _ _ _ hinv hrun (stepsCW_tail hss))
  | .esub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .esub _ _ _ _ _ _ _ _ _ hinv hr hT, .esub hΓ hctx hrun, hss => by
      unfold bwalkAtL
      split
      · exact bhit_closedWf_castTerm _ (bwalkAtL_closedWf k Dom' Val' ss i _ _ _ hinv hrun (stepsCW_tail hss))
      · split
        · exact bhit_closedWf_castTerm _
            (bwalkAtL_closedWf k Dom' Val' ss (i - 1) _ _ _ hinv hrun (stepsCW_tail hss))
        · rename_i hi hj
          generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
          cases e
          exact closedWf_tyCastCtx _ (closedWf_tyCast _ _
            (hss _ (List.Mem.head _)))
  | .lsub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .lsub _ _ _ _ _ _ _ _ _ hinv hr hT, .lsub hΓ hctx hrun, hss => by
      unfold bwalkAtL
      split
      · exact bhit_closedWf_castTerm _ (bwalkAtL_closedWf k Dom' Val' ss i _ _ _ hinv hrun (stepsCW_tail hss))
      · split
        · exact bhit_closedWf_castTerm _
            (bwalkAtL_closedWf k Dom' Val' ss (i - 1) _ _ _ hinv hrun (stepsCW_tail hss))
        · rename_i hi hj
          generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
          cases e
          exact closedWf_tyCastCtx _ (closedWf_tyCast _ _
            (hss _ (List.Mem.head _)))
  | .linst _ _ _ _ _ :: ss, i, A, Γ, h, .linst _ _ _ _ _ hinv, .linst _ _ _ _ _ hrun,
      hss => by
      unfold bwalkAtL
      exact bwalkAtL_closedWf k Dom' Val' ss i _ _ _ hinv hrun (stepsCW_tail hss)
  | .cctx p Askel newTy oldTy u Γr hc :: ss, i, A, Γ, h,
      .cctx _ _ _ _ _ _ _ hinv, .cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun, hss => by
      unfold bwalkAtL
      split
      · rename_i hip
        dsimp only
        split
        · trivial
        · rename_i hv heq
          have hw := bwalkAtL_closedWf k Dom' Val' ss p _ _
            (lookupType_setAssump_at Askel Γ p (hip ▸ h)) hinv hrun (stepsCW_tail hss)
          rw [heq] at hw
          exact closedWf_tyCast _ _ hw
        · rename_i j B hterm hlook hc' heq
          trivial
      · exact bwalkAtL_closedWf k Dom' Val' ss i _ _ _ hinv hrun (stepsCW_tail hss)

/-! ## §4 the walks on typings and the oracle contract -/

/-- `tyAtLet` preserves `ClosedWf`: the transports dissolve into casts, the
    conv nodes read their base typing, and the only carried content — the
    `esub`/`lsub` payload walks — is exactly the `PackL.CW` side condition,
    threaded through the pack transformations (`k` moves under `packLUnder`,
    the skeleton under every push). The induction is the walker's own
    (`tyAtLet.induct`): every recursive appeal is its rank-decreasing edge;
    nothing is ported. -/
theorem tyAtLet_closedWf {E : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs) :
    ∀ {Ei : ResolvedEnv} {nIn : Nat} {Γ : LCtx} {k : Nat}
      {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
      {ss : List (PStep E n)} {e T : Expr Nat}
      (hext : EnvExt Ei E) (p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ)
      (D : TyP Ei nIn Γ e T), p.CW → D.ClosedWf →
      (tyAtLet hW ι ιenv hext p D).ClosedWf := by
  intro Ei nIn Γ k Dom Val Dom' Val' uSlot ss e T hext p D
  induction hW, ι, (fun {E₀} {lhs rhs} => ιenv), hext, p, D using Rcic.Syn.tyAtLet.induct with
  | motive_2 => exact True
  | case1 =>
      intro hCW hD
      simp only [tyAtLet]
      exact closedWf_tyCast _ _ trivial
  | case2 =>
      rename_i Ei n hW1 ι1 ιenv1 hext1 k Dom Val Dom' Val' uSlot ss Γb A i u hlu hA pcl ih1
      intro hCW hD
      simp only [tyAtLet]
      exact finishBvarL_closedWf
        (bwalkAtL_closedWf k Dom' Val' ss i A Γb hlu pcl.inv pcl.run hCW)
  | case3 =>
      intro hCW hD
      simp only [tyAtLet]
      exact closedWf_tyCast _ _ trivial
  | case4 =>
      rename_i ss Γ A u B v hAf hBf dL dF hd pcl ih1 ih2
      intro hCW hD
      simp only [tyAtLet]
      have hAw := ih1 hext pcl hAf hCW hD.1
      have hBw := ih2 hext
        (packLUnder pcl (.assumption A) (.assumption (Skels.app (steps ss) A)) hd) hBf
        (stepsCW_shiftAll _ _ _ hCW) hD.2
      exact closedWf_tyCast _ _ ⟨closedWf_tyCast _ _ hAw,
        closedWf_tyCast _ _ (closedWf_tyCastCtx _ (closedWf_tyCast _ _ hBw))⟩
  | case5 =>
      rename_i ss Γ A u body B v hAf hbodyf hBf dL dF hd pcl ih1 ih2 ih3
      intro hCW hD
      simp only [tyAtLet]
      have hbw := ih2 hext
        (packLUnder pcl (.assumption A) (.assumption (Skels.app (steps ss) A)) hd) hbodyf
        (stepsCW_shiftAll _ _ _ hCW) hD
      exact closedWf_tyCast _ _ (closedWf_tyCastCtx _
        (closedWf_tyCast _ _ hbw))
  | case6 =>
      rename_i f a A B w hf ha hT pcl ih1 ih2 ih3
      intro hCW hD
      simp only [tyAtLet]
      exact closedWf_tyCast _ _
        ⟨closedWf_tyCast _ _ (ih1 hext pcl hf hCW hD.1), ih2 hext pcl ha hCW hD.2⟩
  | case7 =>
      rename_i ss Γ A u value B body w hAf hvf hbf hTf dL dF hd pcl ih1 ih2 ih3 ih4
      intro hCW hD
      simp only [tyAtLet]
      have hbw := ih3 hext
        (packLUnder pcl (.letBinding A value)
          (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value)) hd) hbf
        (stepsCW_shiftAll _ _ _ hCW) hD.2
      exact closedWf_tyCast _ _ ⟨ih2 hext pcl hvf hCW hD.1,
        closedWf_tyCastCtx _ (closedWf_tyCast _ _ hbw)⟩
  | case8 =>
      rename_i ss Γ t T hexp pcl ih1
      intro hCW hD
      simp only [tyAtLet, tyLit]
      exact closedWf_tyCast _ _ (closedWf_tyCast _ _ (ih1 hext pcl hexp hCW hD))
  | case9 =>
      rename_i e A T u h hc pcl ih1 ih2
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 hext pcl h hCW hD
  | case10 =>
      rename_i ss Γ e0 A0 d c Di pcl ih1
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 hext (packLConsWk c d pcl) Di (PackL.CW_wkCons hCW pcl) hD.2
  | case11 =>
      rename_i Di hget hv hvT hget' pcl hv' ih2 ih1
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 hext (packLEsub hget' hv' pcl) Di
        (PackL.CW_esubCons hget' hv' (ih2 hext pcl hv hCW hD.2) hCW pcl) hD.1
  | case12 =>
      rename_i Di hget hv hvT hget' pcl hv' ih2 ih1
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 hext (packLLsub hget' hv' pcl) Di
        (PackL.CW_lsubCons hget' hv' (ih2 hext pcl hv hCW hD.2.2) hCW pcl) hD.2.1
  | case13 =>
      rename_i ls hls pcl13 Di13 ih1
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 hext (packLLinst ls _ _ hls _ pcl13) Di13
        (PackL.CW_linstCons ls _ _ hls _ hCW pcl13) hD
  | case14 =>
      rename_i E₀ hext' Di pcl ih1
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 (envExt_trans hext' hext) pcl Di hCW hD
  | case15 =>
      rename_i Dinner hA pcl pA hc0 hc1 hNew hOld flipped ih2 ih1
      intro hCW hD
      simp only [tyAtLet]
      exact ih1 hext (packLCctx flipped pcl) Dinner
        (PackL.CW_cctxCons flipped hCW pcl) hD
  | _ => trivial

/-- `tyCctxLetAt` is `tyAtLet` at the empty skeleton, where `stepsCW` is
    vacuous. -/
theorem tyCctxLetAt_closedWf {Ei : ResolvedEnv} {E : ResolvedEnv} (hW : CvWalkHyp E)
    (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E) {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {e T : Expr Nat}
    (hget : Γ.get? k = some (.letBinding Dom Val))
    (hslotTy : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hslotVal : CvP E n (Γ.drop (k + 1)) Val Val' Dom)
    (D : TyP Ei n Γ e T) (hD : D.ClosedWf) :
    (tyCctxLetAt hW ι ιenv hext hget hslotTy hslotVal D).ClosedWf :=
  tyAtLet_closedWf hW ι ιenv hext (packNilL hget hslotTy hslotVal) D
    (PackL.CW_nil hget hslotTy hslotVal) hD

/-- **The boundary residue discharged:** the walk-supplied let-context
    conversion preserves `ClosedWf`. -/
theorem letCtxConvP_of_cvWalkHyp_closedWf {E : ResolvedEnv} (w : CvWalkHyp E) {n : Nat} :
    LetCtxConvP.ClosedWf (n := n) (letCtxConvP_of_cvWalkHyp w) := by
  intro Γ A A' v v' e T u hA hv D hD
  simp only [letCtxConvP_of_cvWalkHyp]
  exact tyCctxLetAt_closedWf w (iotaPack_of_cvWalkHyp w)
    (fun hext' h => derivedIotaExt hext' h) (envExt_refl E)
    (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv D hD

/-- **The `EnvWfT`-fronted form:** `letCtxConvP_of_envWfT hW` preserves
    `ClosedWf` — the contract `sortRow_of_allBelowScopedW_letCW` names is
    discharged for the environment-supplied oracle. -/
theorem letCtxConvP_of_envWfT_closedWf {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} :
    LetCtxConvP.ClosedWf (letCtxConvP_of_envWfT (n := n) hW) :=
  letCtxConvP_of_cvWalkHyp_closedWf (cvWalkHyp_of_envWfT hW)

/-- **The boundary, unconditional in the derivation.** The eps-stated
    `sortRow` goal from the epsW pack: the per-link `ClosedWf` of
    `sortRow_of_allBelowScopedW` follows from `hW` alone — the walker's
    ClosedWf-preservation (`tyAtLet` over the `Skels` transport layer)
    supplies the one contract. -/
theorem sortRow_of_allBelowScopedW_envWfT {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl) (hTbl : TableWF tbl)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} (h : TyConvT E n Γ (.sort u) (.sort v)) : eqN u v :=
  sortRow_of_allBelowScopedW_letCW hBel hTbl hW hext hΓ h
    (letCtxConvP_of_envWfT_closedWf hW)

end Rcic.Syn

#print axioms Rcic.Syn.PStep.stepCW
#print axioms Rcic.Syn.stepsCW
#print axioms Rcic.Syn.stepsCW_nil
#print axioms Rcic.Syn.stepsCW_cons
#print axioms Rcic.Syn.stepsCW_tail
#print axioms Rcic.Syn.stepCW_shiftStep
#print axioms Rcic.Syn.stepsCW_shiftAll
#print axioms Rcic.Syn.PackL.CW
#print axioms Rcic.Syn.PackL.CW_nil
#print axioms Rcic.Syn.PackL.CW_wkCons
#print axioms Rcic.Syn.PackL.CW_esubCons
#print axioms Rcic.Syn.PackL.CW_lsubCons
#print axioms Rcic.Syn.PackL.CW_linstCons
#print axioms Rcic.Syn.PackL.CW_cctxCons
#print axioms Rcic.Syn.PackL.CW_under
#print axioms Rcic.Syn.closedWf_convChain
#print axioms Rcic.Syn.BHit.ClosedWf
#print axioms Rcic.Syn.bhit_closedWf_castTerm
#print axioms Rcic.Syn.retypeLetBVarSlot_closedWf
#print axioms Rcic.Syn.finishBvarL_closedWf
#print axioms Rcic.Syn.bwalkAtL_closedWf
#print axioms Rcic.Syn.tyAtLet_closedWf
#print axioms Rcic.Syn.tyCctxLetAt_closedWf
#print axioms Rcic.Syn.letCtxConvP_of_cvWalkHyp_closedWf
#print axioms Rcic.Syn.letCtxConvP_of_envWfT_closedWf
#print axioms Rcic.Syn.sortRow_of_allBelowScopedW_envWfT