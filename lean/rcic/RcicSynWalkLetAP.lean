import rcic.RcicSynEnrich

/-!
# `AssumpPref` through the let-slot walk (Q7 totality, step 4k)

`letCtxConvP_of_cvWalkHyp` (RcicSynEnrich) rewrites a `.letBinding` slot via the
let-slot walk `tyAtLet`/`cvAtLet` (RcicSynWalkLet). This module proves the walk
preserves `AssumpPref`: every transport node it emits satisfies
`AssumptionPrefix` at its cutoff whenever the inputs do.

The reason this holds: the walk never re-emits an input transport at its
original cutoff. The only transport nodes materialized in the output are
- the cutoff-`0` `wk`s built by `wkFront`/`cvFront` (and by `shiftStep` on
  stored evidence), and
- the stored `PStep` evidence (`esub`/`lsub` replacements, `cctx`
  conversions), which is itself produced by recursive `tyAtLet`/`cvAtLet`
  calls, hence covered by the induction hypothesis.

`AssumptionPrefix _ 0` is trivial (`assumptionPrefix_zero`), so the generated
transports are all discharged. What makes the proof tedious is that
`wkFront`/`cvFront`/`retypeLetBVarSlot`/`retypeLetBValSlot`/`packLUnder`
assemble their outputs through `Eq.mpr` casts of *bundled* type equalities
(`TyP .. = TyP ..` with several components at once), which cannot be
`cases`-eliminated directly. We peel them with `assumpPref_mprTyP`/
`assumpPref_mprCvP`, which take the component equalities separately.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 bundled-`Eq.mpr` eliminators -/

/-- `AssumpPref` survives a bundled type-equality cast once the components are
    given separately. `Eq.mpr h : TyP Γ' e' T' → TyP Γ e T` for
    `h : TyP Γ e T = TyP Γ' e' T'`. -/
theorem assumpPref_mprTyP {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    {e e' T T' : Expr Nat} (hΓ : Γ = Γ') (he : e = e') (hT : T = T')
    (D : TyP E n Γ' e' T') (h : TyP E n Γ e T = TyP E n Γ' e' T') :
    D.AssumpPref → (Eq.mpr h D).AssumpPref := by
  cases hΓ; cases he; cases hT
  rw [Subsingleton.elim h (Eq.refl _)]
  exact id

/-- `CvP` analogue. -/
theorem assumpPref_mprCvP {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    {a a' b b' T T' : Expr Nat} (hΓ : Γ = Γ') (ha : a = a') (hb : b = b')
    (hT : T = T')
    (C : CvP E n Γ' a' b' T') (h : CvP E n Γ a b T = CvP E n Γ' a' b' T') :
    C.AssumpPref → (Eq.mpr h C).AssumpPref := by
  cases hΓ; cases ha; cases hb; cases hT
  rw [Subsingleton.elim h (Eq.refl _)]
  exact id

/-- `CvP` two-layer `Eq.mpr` eliminator: a `rw`-cast tower `Eq.mpr e₂ (Eq.mpr e₁ C)`
    collapses to `C` once every index equality is closed. -/
theorem assumpPref_mprCvP2 {E : ResolvedEnv} {n : Nat}
    {Γ Γ₁ Γ₂ : LCtx} {a a₁ a₂ b b₁ b₂ T T₁ T₂ : Expr Nat}
    (hΓ₁ : Γ₁ = Γ) (ha₁ : a₁ = a) (hb₁ : b₁ = b) (hT₁ : T₁ = T)
    (hΓ₂ : Γ₂ = Γ) (ha₂ : a₂ = a) (hb₂ : b₂ = b) (hT₂ : T₂ = T)
    (C : CvP E n Γ a b T)
    (e₁ : CvP E n Γ₁ a₁ b₁ T₁ = CvP E n Γ a b T)
    (e₂ : CvP E n Γ₂ a₂ b₂ T₂ = CvP E n Γ₁ a₁ b₁ T₁) :
    C.AssumpPref → (Eq.mpr e₂ (Eq.mpr e₁ C)).AssumpPref := by
  cases hΓ₁; cases ha₁; cases hb₁; cases hT₁
  cases hΓ₂; cases ha₂; cases hb₂; cases hT₂
  cases e₁; cases e₂
  exact id

/-! ## §2 evidence carried by the skeleton -/

/-- The stored evidence of one `PStep`: `esub`/`lsub` replacements and `cctx`
    conversions are typed derivations and must satisfy `AssumpPref`. -/
def pStepAP {E : ResolvedEnv} {n : Nat} : PStep E n → Prop
| .esub _ _ _ _ _ _ _ _ hv => hv.AssumpPref
| .lsub _ _ _ _ _ _ _ _ hv => hv.AssumpPref
| .cctx _ _ _ _ _ _ hc => hc.AssumpPref
| _ => True

def pStepsAP {E : ResolvedEnv} {n : Nat} : List (PStep E n) → Prop
| [] => True
| s :: ss => pStepAP s ∧ pStepsAP ss

theorem pStepsAP_cons {E : ResolvedEnv} {n : Nat} (s : PStep E n)
    {ss : List (PStep E n)} (h : pStepAP s) (t : pStepsAP ss) :
    pStepsAP (s :: ss) := ⟨h, t⟩

/-- A cutoff-`0` `wk` node preserves `AssumpPref`. -/
theorem assumpPref_wkZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {d : LocalDecl} {D : TyP E n Γ e T}
    (hD : D.AssumpPref) : (TyP.wk E n Γ e T d 0 D).AssumpPref :=
  ⟨assumptionPrefix_zero Γ, hD⟩

theorem assumpPref_cvWkZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {d : LocalDecl} {C : CvP E n Γ a b T}
    (hC : C.AssumpPref) : (CvP.wk E n Γ a b T d 0 C).AssumpPref :=
  ⟨assumptionPrefix_zero Γ, hC⟩

/-- `shiftStep` re-wraps stored evidence at cutoff `0`, preserving AP. -/
theorem pStepAP_shiftStep {E : ResolvedEnv} {n : Nat} (dLocal dFinal : LocalDecl) :
    ∀ (s : PStep E n), pStepAP s → pStepAP (shiftStep dLocal dFinal s)
| .wk _ _, _ => trivial
| .esub _ _ _ _ _ _ _ _ _, hs => assumpPref_wkZero hs
| .lsub _ _ _ _ _ _ _ _ _, hs => assumpPref_wkZero hs
| .linst _ _ _ _ _, _ => trivial
| .cctx _ _ _ _ _ _ _, hs =>
      assumpPref_cvCast _ _ _ (assumpPref_cvWkZero hs)

theorem pStepsAP_shiftAll {E : ResolvedEnv} {n : Nat} (dLocal dFinal : LocalDecl) :
    ∀ (ss : List (PStep E n)), pStepsAP ss → pStepsAP (shiftAll dLocal dFinal ss)
| [], _ => trivial
| s :: ss, hs =>
      ⟨pStepAP_shiftStep dLocal dFinal s hs.1,
        pStepsAP_shiftAll (Skel.onDecl s.sk dLocal) dFinal ss hs.2⟩

/-! ## §3 `ConvChain` -/

/-- Every link of a conversion chain satisfies `AssumpPref`. -/
def convChainAP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat} :
    ConvChain E n Γ a b → Prop
| .nil => True
| .cons _ h rest => h.AssumpPref ∧ convChainAP rest

theorem convChainAP_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c : Expr Nat}
    (u : Level) (h : CvP E n Γ b c (.sort u)) :
    ∀ (cc : ConvChain E n Γ a b), convChainAP cc → h.AssumpPref →
      convChainAP (cc.snoc u h)
| .nil, _, hh => ⟨hh, trivial⟩
| .cons _ _ rest, hcc, hh => ⟨hcc.1, convChainAP_snoc u h rest hcc.2 hh⟩

/-- `ConvChain.apply` emits one `TyP.conv` per link. -/
theorem assumpPref_convChain_apply {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e a c : Expr Nat} (h : TyP E n Γ e a) :
    ∀ (cc : ConvChain E n Γ a c), h.AssumpPref → convChainAP cc →
      (cc.apply h).AssumpPref
| .nil, hh, _ => hh
| .cons _ _ rest, hh, hcc =>
      assumpPref_convChain_apply _ rest ⟨hh, hcc.1⟩ hcc.2

/-- `chainSort` returns either `hA` or the last link's `dl`. -/
theorem assumpPref_chainSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {B ty : Expr Nat} {u0 : Level}
    (hA : TyP E n Γ ty (.sort u0)) :
    ∀ (hc : ConvChain E n Γ B ty), hA.AssumpPref → convChainAP hc →
      (chainSort hA hc).2.AssumpPref
| .nil, hh, _ => hh
| .cons _ _ _, _, hccap => assumpPref_dl hccap.1

/-! ## §4 `BHit` and the variable walk -/

/-- `BHit` payload: a `repl` carries the stored replacement typing; a `retype`
    carries a conversion chain; `keep` is proof-only. -/
def bHitAP {E : ResolvedEnv} {n : Nat} {pre fin : LCtx} {term ty : Expr Nat} :
    BHit E n pre fin term ty → Prop
| .keep _ _ _ => True
| .repl hv => hv.AssumpPref
| .retype _ _ _ _ hc => convChainAP hc

theorem bHitAP_castTerm {E : ResolvedEnv} {n : Nat} {pre fin : LCtx}
    {term ty term' : Expr Nat} (h : term' = term) :
    ∀ (w : BHit E n pre fin term ty), bHitAP w → bHitAP (w.castTerm h)
| .keep _ _ _, _ => trivial
| .repl _, hw => assumpPref_tyCast _ _ hw
| .retype _ _ _ _ _, hw => hw

/-- The let-slot `bwalkAtL`: every result's payload is AP. The only payloads
    are `stepsAP`-stored evidence (re-wrapped in casts) and one-link/snoc'd
    `cctx` chains. -/
theorem bwalkAtL_ap {n : Nat} (k : Nat) (Dom' Val' : Expr Nat) :
    ∀ (ss : List (PStep E n)) (i : Nat) (A : Expr Nat) (Γ : LCtx)
      (h : lookupType Γ i = some A) (inv : EsInv ss)
      (run : RunL k Dom' Val' ss Γ), pStepsAP ss →
      bHitAP (bwalkAtL k Dom' Val' ss i A Γ h inv run)
| [], _, _, _, _, _, _, _ => by
      unfold bwalkAtL bHitAP; trivial
| .wk c d :: ss, i, A, Γ, h, .wk _ _ hinv, .wk _ _ hrun, hs => by
      unfold bwalkAtL
      split
      · exact bHitAP_castTerm _ _ (bwalkAtL_ap k Dom' Val' ss i _ _ _ hinv hrun hs.2)
      · exact bHitAP_castTerm _ _ (bwalkAtL_ap k Dom' Val' ss (i + 1) _ _ _ hinv hrun hs.2)
| .esub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .esub _ _ _ _ _ _ _ _ _ hinv hr hT, .esub hΓ hctx hrun, hs => by
      unfold bwalkAtL
      split
      · exact bHitAP_castTerm _ _ (bwalkAtL_ap k Dom' Val' ss i _ _ _ hinv hrun hs.2)
      · split
        · exact bHitAP_castTerm _ _
            (bwalkAtL_ap k Dom' Val' ss (i - 1) _ _ _ hinv hrun hs.2)
        · rename_i hi hj
          generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj)
              (Nat.le_of_not_lt hi) = e
          cases e
          exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ hs.1)
| .lsub j v t Γe Γr hget repl replT hv :: ss, i, A, Γ, h,
      .lsub _ _ _ _ _ _ _ _ _ hinv hr hT, .lsub hΓ hctx hrun, hs => by
      unfold bwalkAtL
      split
      · exact bHitAP_castTerm _ _ (bwalkAtL_ap k Dom' Val' ss i _ _ _ hinv hrun hs.2)
      · split
        · exact bHitAP_castTerm _ _
            (bwalkAtL_ap k Dom' Val' ss (i - 1) _ _ _ hinv hrun hs.2)
        · rename_i hi hj
          generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj)
              (Nat.le_of_not_lt hi) = e
          cases e
          exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ hs.1)
| .linst _ _ _ _ _ :: ss, i, A, Γ, h, .linst _ _ _ _ _ hinv, .linst _ _ _ _ _ hrun,
      hs => by
      unfold bwalkAtL
      exact bwalkAtL_ap k Dom' Val' ss i _ _ _ hinv hrun hs.2
| .cctx p Askel newTy oldTy u Γr hc :: ss, i, A, Γ, h,
      .cctx _ _ _ _ _ _ _ hinv, .cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun,
      hs => by
      unfold bwalkAtL
      split
      · rename_i hip
        dsimp only
        split
        · exact ⟨assumpPref_cvCastCtx _ (assumpPref_cvCast _ _ _ hs.1), trivial⟩
        · rename_i hv' heq
          have hw := bwalkAtL_ap k Dom' Val' ss p _ _
            (lookupType_setAssump_at Askel Γ p (hip ▸ h)) hinv hrun hs.2
          rw [heq] at hw
          exact assumpPref_tyCast _ _
            ⟨hw, assumpPref_cvCastCtx _ (assumpPref_cvCast _ _ _ hs.1)⟩
        · rename_i j B hterm hlook hc' heq
          have hw := bwalkAtL_ap k Dom' Val' ss p _ _
            (lookupType_setAssump_at Askel Γ p (hip ▸ h)) hinv hrun hs.2
          rw [heq] at hw
          exact convChainAP_snoc _ _ _ hw
            (assumpPref_cvCastCtx _ (assumpPref_cvCast _ _ _ hs.1))
      · exact bwalkAtL_ap k Dom' Val' ss i A _ _ hinv hrun hs.2

/-! ## §5 `wkFront`/`cvFront`: iterated cutoff-`0` weakening -/

/-- `Eq.mpr` towers fuse along `Eq.trans` — used to collapse the per-`rw`
    casts that `wkFront`/`cvFront` nil arms emit. -/
theorem eqMpr_trans {α β γ : Type} (h : α = β) (h' : β = γ) (x : γ) :
    Eq.mpr h (Eq.mpr h' x) = Eq.mpr (h.trans h') x := by
  cases h; cases h'; rfl

/-- `wkFront ds` stacks `|ds|` cutoff-`0` `wk` nodes (plus one bundled cast in
    the nil arm); every emitted transport is at cutoff `0`. -/
theorem assumpPref_wkFront {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} :
    ∀ (ds : List LocalDecl) (D : TyP E n Γ e T), D.AssumpPref →
      (wkFront ds D).AssumpPref
| [], D, hD => by
      unfold wkFront
      rw [eqMpr_trans, eqMpr_trans, eqMpr_trans]
      exact assumpPref_mprTyP rfl (lift_zero 0 e) (lift_zero 0 T) D _ hD
| _ :: ds, D, hD => by
      unfold wkFront
      exact assumpPref_tyCast _ _ (assumpPref_wkZero (assumpPref_wkFront ds D hD))

theorem assumpPref_cvFront {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} :
    ∀ (ds : List LocalDecl) (C : CvP E n Γ a b T), C.AssumpPref →
      (cvFront ds C).AssumpPref
| [], C, hC => by
      unfold cvFront
      rw [eqMpr_trans, eqMpr_trans, eqMpr_trans, eqMpr_trans]
      exact assumpPref_mprCvP rfl (lift_zero 0 a) (lift_zero 0 b)
        (lift_zero 0 T) C _ hC
| _ :: ds, C, hC =>
      assumpPref_cvCast _ _ _ (assumpPref_cvWkZero (assumpPref_cvFront ds C hC))

/-! ## §6 `PackL` payloads -/

/-- The AP invariant of a `PackL`: every stored `PStep` payload plus the two
    slot conversions. -/
def packLAP {E : ResolvedEnv} {n k : Nat} {Dom Val Dom' Val' : Expr Nat}
    {uSlot : Level} {nIn : Nat} {ss : List (PStep E n)} {Γ : LCtx}
    (_p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ) : Prop :=
  pStepsAP ss ∧ _p.slotTy.AssumpPref ∧ _p.slotVal.AssumpPref

theorem packLAP_nil {E : ResolvedEnv} {n k : Nat} {Γ : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {hget : Γ.get? k = some (.letBinding Dom Val)}
    {hslotTy : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot)}
    {hslotVal : CvP E n (Γ.drop (k + 1)) Val Val' Dom}
    (hT : hslotTy.AssumpPref) (hV : hslotVal.AssumpPref) :
    packLAP (packNilL hget hslotTy hslotVal) := ⟨trivial, hT, hV⟩

theorem packLAP_wk {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} (d : LocalDecl)
    {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (insertAt d 0 Γ)}
    (hp : packLAP p) : packLAP (packLWk d p) := ⟨⟨trivial, hp.1⟩, hp.2⟩

theorem packLAP_consWk {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} (c : Nat) (d : LocalDecl)
    {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (insertAt d c Γ)}
    (hp : packLAP p) : packLAP (packLConsWk c d p) := ⟨⟨trivial, hp.1⟩, hp.2⟩

theorem packLAP_linst {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level}
    {ss : List (PStep E n)} {Γ : LCtx} (ls : List Level) (a nStep : Nat)
    (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
    {p : PackL E n k Dom Val Dom' Val' uSlot nStep ss (instLvlsCtx ls Γ)}
    (hp : packLAP p) : packLAP (packLLinst ls a nStep hls hlen p) :=
  ⟨⟨trivial, hp.1⟩, hp.2⟩

theorem packLAP_esub {n k j : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.assumption t))
    {hv : TyP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))}
    (hvap : hv.AssumpPref)
    {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ)}
    (hp : packLAP p) : packLAP (packLEsub hget hv p) := ⟨⟨hvap, hp.1⟩, hp.2⟩

theorem packLAP_lsub {n k j : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {v t : Expr Nat}
    (hget : Γ.get? j = some (.letBinding t v))
    {hv : TyP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ)))
      (Skels.app (steps ss) (lift 0 j v)) (Skels.app (steps ss) (lift 0 j t))}
    (hvap : hv.AssumpPref)
    {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (substRemove v j Γ)}
    (hp : packLAP p) : packLAP (packLLsub hget hv p) := ⟨⟨hvap, hp.1⟩, hp.2⟩

theorem packLAP_cctx {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {A A' : Expr Nat} {u : Level}
    {hc : CvP E n (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ)))
      (Skels.app (steps ss) (lift 0 1 A')) (Skels.app (steps ss) (lift 0 1 A))
      (.sort u)}
    (hcap : hc.AssumpPref)
    {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss (.assumption A' :: Γ)}
    (hp : packLAP p) : packLAP (packLCctx hc p) := ⟨⟨hcap, hp.1⟩, hp.2⟩

/-- `packLUnder` rewrites the two slot conversions along `steps_shiftAll` and
    `drop_shift`; both are bundled `Eq.mpr` casts. -/
theorem packLAP_under {n k : Nat} {Dom Val Dom' Val' : Expr Nat} {uSlot : Level} {nIn : Nat}
    {ss : List (PStep E n)} {Γ : LCtx}
    {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ}
    (dLocal dFinal : LocalDecl)
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    (hp : packLAP p) : packLAP (packLUnder p dLocal dFinal hd) := by
  have hΓ : (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)).drop
        (k + 1 + 1)
      = (Skels.ctx (steps ss) Γ).drop (k + 1) := by
    rw [steps_shiftAll]; exact drop_shift _ _ _ _
  refine ⟨pStepsAP_shiftAll _ _ _ hp.1, ?_, ?_⟩
  · unfold packLUnder
    dsimp only
    exact assumpPref_mprCvP2 (drop_shift _ _ _ _) rfl rfl rfl
      hΓ rfl rfl rfl p.slotTy _ _ hp.2.1
  · unfold packLUnder
    dsimp only
    exact assumpPref_mprCvP2 (drop_shift _ _ _ _) rfl rfl rfl
      hΓ rfl rfl rfl p.slotVal _ _ hp.2.2

/-! ## §7 slot retyping, `finishBvarL`, `moveUnder` -/

/-- The `hpref ▸` cutoff casts inside `retypeLetB*Slot` are `Eq.rec`
    transports on the variable-headed length equality `l = m`; `cases` on the
    hypothesis collapses the cast to the identity. -/
theorem assumpPref_drecTyL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e srt : Expr Nat} {l m : Nat} {h : l = m}
    {D : TyP E n Γ (lift 0 l e) (lift 0 l srt)} :
    D.AssumpPref → (h ▸ D).AssumpPref := by
  cases h; exact id

/-- `CvP` analogue of `assumpPref_drecTyL`. -/
theorem assumpPref_drecCvL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b srt : Expr Nat} {l m : Nat} {h : l = m}
    {C : CvP E n Γ (lift 0 l a) (lift 0 l b) (lift 0 l srt)} :
    C.AssumpPref → (h ▸ C).AssumpPref := by
  cases h; exact id

theorem assumpPref_retypeLetBVarSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {k : Nat} {Dom Val Dom' Val' : Expr Nat} {u : Level}
    {h : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u)}
    (hap : h.AssumpPref)
    (hget : Γ.get? k = some (.letBinding Dom Val)) :
    (retypeLetBVarSlot (Val' := Val') h hget).AssumpPref := by
  unfold retypeLetBVarSlot
  dsimp only
  refine ⟨?_, ?_⟩
  · exact assumpPref_tyCastCtx _
      (assumpPref_drecTyL (assumpPref_wkFront _ _ (assumpPref_dr hap)))
  · exact assumpPref_cvCastCtx _
      (assumpPref_drecCvL
        (assumpPref_cvFront _
          (CvP.symm E n (Γ.drop (k + 1)) Dom Dom' (.sort u) h h.dr h.dl)
          ⟨hap, assumpPref_dr hap, assumpPref_dl hap⟩))

theorem assumpPref_retypeLetBValSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {k : Nat} {Dom Val Dom' Val' : Expr Nat} {u : Level}
    {hA : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u)}
    {hv : CvP E n (Γ.drop (k + 1)) Val Val' Dom}
    (hapA : hA.AssumpPref) (hapv : hv.AssumpPref)
    (hget : Γ.get? k = some (.letBinding Dom Val)) :
    (retypeLetBValSlot hA hv hget).AssumpPref := by
  unfold retypeLetBValSlot
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- hz' = tyConv hz hdomSymm' dl' hv'1
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- hz = zetaLocal .. hv' hb hv'; hv' = conv hv'1 hdomC
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨assumpPref_tyCastCtx _
          (assumpPref_drecTyL (assumpPref_wkFront _ _ (assumpPref_dr hapv))),
          assumpPref_cvCastCtx _
            (assumpPref_drecCvL (assumpPref_cvFront _ hA hapA))⟩
      · exact assumpPref_tyCastCtx _
          (assumpPref_drecTyL (assumpPref_wkFront _ _ (assumpPref_dr hapA)))
      · exact ⟨assumpPref_tyCastCtx _
          (assumpPref_drecTyL (assumpPref_wkFront _ _ (assumpPref_dr hapv))),
          assumpPref_cvCastCtx _
            (assumpPref_drecCvL (assumpPref_cvFront _ hA hapA))⟩
    · exact assumpPref_cvCastCtx _
        (assumpPref_drecCvL (assumpPref_cvFront _
          (CvP.symm E n (Γ.drop (k + 1)) Dom Dom' (.sort u) hA hA.dr hA.dl)
          ⟨hapA, assumpPref_dr hapA, assumpPref_dl hapA⟩))
    · exact assumpPref_retypeLetBVarSlot hapA hget
    · exact assumpPref_tyCastCtx _
        (assumpPref_drecTyL (assumpPref_wkFront _ _ (assumpPref_dr hapv)))
  · exact assumpPref_cvCastCtx _
      (assumpPref_drecCvL (assumpPref_cvFront _
        (CvP.symm E n (Γ.drop (k + 1)) Val Val' Dom hv hv.dr hv.dl)
        ⟨hapv, assumpPref_dr hapv, assumpPref_dl hapv⟩))
  · exact assumpPref_retypeLetBVarSlot hapA hget
  · exact assumpPref_tyCastCtx _
      (assumpPref_drecTyL (assumpPref_wkFront _ _ (assumpPref_dl hapv)))

/-- `finishBvarL` preserves AP when the slot conversion, the typing child `hA`,
    and the walk hit payload all do. -/
theorem assumpPref_finishBvarL {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level}
    {term ty : Expr Nat}
    {hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot)}
    {hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u)}
    (hgete : Γpre.get? k = some (.letBinding Dom Val))
    (hslotA : hslot.AssumpPref) (hAA : hA.AssumpPref)
    {w : BHit E n Γpre (setLetB k Dom' Val' Γpre) term ty}
    (hw : bHitAP w) :
    (finishBvarL hgete hslot hA w).AssumpPref := by
  unfold finishBvarL
  dsimp only
  cases w with
| repl hv => exact hw
| keep j hterm hlook =>
      dsimp only
      split
      · exact assumpPref_tyCast _ _
          (assumpPref_retypeLetBVarSlot hslotA hgete)
      · exact assumpPref_tyCast _ _ hAA
| retype j B hterm hlook hc =>
      dsimp only
      split
      · exact assumpPref_convChain_apply _ hc
          (assumpPref_tyCast _ _
            (assumpPref_retypeLetBVarSlot hslotA hgete)) hw
      · exact assumpPref_convChain_apply _ hc
          (assumpPref_tyCast _ _
            (assumpPref_chainSort _ hc hAA hw)) hw

/-- `moveUnderL` is `tyCastCtx (tyCast h)` — AP carries through. -/
theorem assumpPref_moveUnderL {n k : Nat} {Dom' Val' : Expr Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {dLocal dFinal : LocalDecl}
    {body T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    {h : TyP E n
      (setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) body)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T)}
    (hap : h.AssumpPref) :
    (moveUnderL hd h).AssumpPref := by
  unfold moveUnderL
  exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ hap)

/-- `moveUnderCvL` is `cvCastCtx (cvCast h)` — AP carries through. -/
theorem assumpPref_moveUnderCvL {n k : Nat} {Dom' Val' : Expr Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {dLocal dFinal : LocalDecl}
    {a b T : Expr Nat}
    (hd : dFinal = Skels.onDecl (steps ss) dLocal)
    {h : CvP E n
      (setLetB (k + 1) Dom' Val'
        (Skels.ctx (steps (shiftAll dLocal dFinal ss)) (dLocal :: Γ)))
      (Skels.app (steps (shiftAll dLocal dFinal ss)) a)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) b)
      (Skels.app (steps (shiftAll dLocal dFinal ss)) T)}
    (hap : h.AssumpPref) :
    (moveUnderCvL hd h).AssumpPref := by
  unfold moveUnderCvL
  exact assumpPref_cvCastCtx _ (assumpPref_cvCast _ _ _ hap)

/-! ## §8 skeleton-app casts and emitters -/

theorem assumpPref_toSort {n : Nat} {Γ : LCtx} {e : Expr Nat} {ss : List Skel}
    {u : Level} {h : TyP E n Γ e (Skels.app ss (.sort u))}
    (hh : h.AssumpPref) : (toSort h).AssumpPref := assumpPref_tyCast _ _ hh

theorem assumpPref_toSortZero {n : Nat} {Γ : LCtx} {e : Expr Nat}
    {ss : List Skel} {h : TyP E n Γ e (Skels.app ss (.sort .zero))}
    (hh : h.AssumpPref) : (toSortZero h).AssumpPref := assumpPref_tyCast _ _ hh

theorem assumpPref_toPi {n : Nat} {Γ : LCtx} {f : Expr Nat} {ss : List Skel}
    {A B : Expr Nat} {h : TyP E n Γ f (Skels.app ss (.pi A B))}
    (hh : h.AssumpPref) : (toPi h).AssumpPref := assumpPref_tyCast _ _ hh

theorem assumpPref_cvToSort {n : Nat} {Γ : LCtx} {a b : Expr Nat}
    {ss : List Skel} {u : Level}
    {h : CvP E n Γ a b (Skels.app ss (.sort u))}
    (hh : h.AssumpPref) : (cvToSort h).AssumpPref := assumpPref_cvCast _ _ _ hh

theorem assumpPref_cvToPi {n : Nat} {Γ : LCtx} {f g : Expr Nat}
    {ss : List Skel} {A B : Expr Nat}
    {h : CvP E n Γ f g (Skels.app ss (.pi A B))}
    (hh : h.AssumpPref) : (cvToPi h).AssumpPref := assumpPref_cvCast _ _ _ hh

theorem assumpPref_tySort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (l k : Level) (h : eqN k (.succ l)) (ss : List Skel) :
    (tySort (E := E) (n := n) (Γ := Γ) l k h ss).AssumpPref := by
  exact assumpPref_tyCast _ _ True.intro

theorem assumpPref_tyConst {E : ResolvedEnv} (hW : CvWalkHyp E) {n nIn : Nat}
    {Γ : LCtx} {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true) (hls : eqNList ls ls₀)
    (ss : List (PStep E n)) (hfuel : FuelRel ss nIn)
    {hT : TyP E n Γ
      (Skels.app (steps ss) (instantiateLevels ls₀ m.mtype))
      (.sort (Skels.appLevel (steps ss) u))}
    (hTap : hT.AssumpPref) :
    (tyConst hW hres hlen hwf hls ss hfuel hT).AssumpPref := by
  refine assumpPref_tyCast _ _ ?_
  exact assumpPref_tyCast _ _ hTap

theorem assumpPref_tyPi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A B : Expr Nat) (u v : Level) (ss : List Skel)
    {hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u))}
    {hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) B) (.sort (Skels.appLevel (ss.map Skel.shift) v))}
    (ha : hA.AssumpPref) (hb : hB.AssumpPref) :
    (tyPi A B u v ss hA hB).AssumpPref := by
  refine assumpPref_tyCast _ _ ?_
  exact ⟨ha, hb⟩

theorem assumpPref_tyLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A body B : Expr Nat) (u v : Level) (ss : List Skel)
    {hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u))}
    {hbody : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B)}
    {hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) B) (.sort (Skels.appLevel (ss.map Skel.shift) v))}
    (ha : hA.AssumpPref) (hbo : hbody.AssumpPref) (hb : hB.AssumpPref) :
    (tyLam A body B u v ss hA hbody hB).AssumpPref := by
  refine assumpPref_tyCast _ _ ?_
  exact ⟨ha, hbo, hb⟩

theorem assumpPref_tyApp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (f a A B : Expr Nat) (w : Level) (ss : List Skel)
    {hf : TyP E n Γ (Skels.app ss f)
      (.pi (Skels.app ss A) (Skels.app (ss.map Skel.shift) B))}
    {ha : TyP E n Γ (Skels.app ss a) (Skels.app ss A)}
    {hT : TyP E n Γ (Skels.app ss (instantiate0 a B))
      (.sort (Skels.appLevel ss w))}
    (hfap : hf.AssumpPref) (haap : ha.AssumpPref) (hTap : hT.AssumpPref) :
    (tyApp f a A B w ss hf ha hT).AssumpPref := by
  refine assumpPref_tyCast _ _ ?_
  refine ⟨hfap, haap, ?_⟩
  exact assumpPref_tyCast _ _ hTap

theorem assumpPref_tyLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A value B body : Expr Nat) (u w : Level) (ss : List Skel)
    {hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u))}
    {hv : TyP E n Γ (Skels.app ss value) (Skels.app ss A)}
    {hb : TyP E n (.letBinding (Skels.app ss A) (Skels.app ss value) :: Γ)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B)}
    {hT : TyP E n Γ (Skels.app ss (instantiate0 value B))
      (.sort (Skels.appLevel ss w))}
    (ha : hA.AssumpPref) (hvap : hv.AssumpPref) (hbap : hb.AssumpPref)
    (hTap : hT.AssumpPref) :
    (tyLet A value B body u w ss hA hv hb hT).AssumpPref := by
  refine assumpPref_tyCast _ _ ?_
  refine ⟨ha, hvap, hbap, ?_⟩
  exact assumpPref_tyCast _ _ hTap

theorem assumpPref_tyLit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (t : Nat)
    (T : Expr Nat) (ss : List Skel)
    {hexp : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T)}
    (hh : hexp.AssumpPref) : (tyLit t T ss hexp).AssumpPref := by
  unfold tyLit
  refine assumpPref_tyCast _ _ ?_
  exact assumpPref_tyCast _ _ hh

theorem assumpPref_cvBeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (A body arg B : Expr Nat) (u : Level)
    {hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u))}
    {hbody : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B)}
    {harg : TyP E n Γ (Skels.app ss arg) (Skels.app ss A)}
    {dl : TyP E n Γ (Skels.app ss (.app (.lam A body) arg))
      (Skels.app ss (instantiate0 arg B))}
    {dr : TyP E n Γ (Skels.app ss (instantiate0 arg body))
      (Skels.app ss (instantiate0 arg B))}
    (ha : hA.AssumpPref) (hbo : hbody.AssumpPref) (har : harg.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvBeta ss A body arg B u hA hbody harg dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨ha, hbo, har, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvZeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (A value body B : Expr Nat) (u : Level)
    {hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u))}
    {hv : TyP E n Γ (Skels.app ss value) (Skels.app ss A)}
    {hb : TyP E n (.letBinding (Skels.app ss A) (Skels.app ss value) :: Γ)
      (Skels.app (ss.map Skel.shift) body) (Skels.app (ss.map Skel.shift) B)}
    {dl : TyP E n Γ (Skels.app ss (.letE A value body))
      (Skels.app ss (instantiate0 value B))}
    {dr : TyP E n Γ (Skels.app ss (instantiate0 value body))
      (Skels.app ss (instantiate0 value B))}
    (ha : hA.AssumpPref) (hvap : hv.AssumpPref) (hbap : hb.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvZeta ss A value body B u hA hv hb dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨ha, hvap, hbap, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvDelta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : CvWalkHyp E) (ss : List (PStep E n)) (nIn : Nat) (hfuel : FuelRel ss nIn)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true)
    {hb : TyP E n Γ (Skels.app (steps ss) (instantiateLevels ls b))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))}
    {dl : TyP E n Γ (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))}
    {dr : TyP E n Γ (Skels.app (steps ss) (instantiateLevels ls b))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))}
    (hbap : hb.AssumpPref) (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvDelta hW ss nIn hfuel hres hbody htr hlen hwf hb dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨?_, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hbap
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvLit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (t : Nat) (T : Expr Nat)
    {hexp : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T)}
    {dl : TyP E n Γ (Skels.app ss (.lit t)) (Skels.app ss T)}
    {dr : TyP E n Γ (Skels.app ss (natExpand t)) (Skels.app ss T)}
    (hh : hexp.AssumpPref) (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvLit ss t T hexp dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨?_, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hh
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvApp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (f g a b A B : Expr Nat)
    {h1 : CvP E n Γ (Skels.app ss f) (Skels.app ss g) (Skels.app ss (.pi A B))}
    {h2 : CvP E n Γ (Skels.app ss a) (Skels.app ss b) (Skels.app ss A)}
    {dl : TyP E n Γ (Skels.app ss (.app f a)) (Skels.app ss (instantiate0 a B))}
    {dr : TyP E n Γ (Skels.app ss (.app g b)) (Skels.app ss (instantiate0 a B))}
    (h1ap : h1.AssumpPref) (h2ap : h2.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvApp ss f g a b A B h1 h2 dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨?_, h2ap, ?_, ?_⟩
  · exact assumpPref_cvToPi h1ap
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (A A' b b' B : Expr Nat) (u : Level)
    {hA : CvP E n Γ (Skels.app ss A) (Skels.app ss A')
      (.sort (Skels.appLevel ss u))}
    {hb : CvP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) b) (Skels.app (ss.map Skel.shift) b')
      (Skels.app (ss.map Skel.shift) B)}
    {dl : TyP E n Γ (Skels.app ss (.lam A b)) (Skels.app ss (.pi A B))}
    {dr : TyP E n Γ (Skels.app ss (.lam A' b')) (Skels.app ss (.pi A B))}
    (ha : hA.AssumpPref) (hbap : hb.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvLam ss A A' b b' B u hA hb dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨ha, hbap, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvPi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (A A' B B' : Expr Nat) (u v : Level)
    {hA : CvP E n Γ (Skels.app ss A) (Skels.app ss A')
      (.sort (Skels.appLevel ss u))}
    {hB : CvP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) B) (Skels.app (ss.map Skel.shift) B')
      (.sort (Skels.appLevel (ss.map Skel.shift) v))}
    {dl : TyP E n Γ (Skels.app ss (.pi A B)) (Skels.app ss (.sort (.imax u v)))}
    {dr : TyP E n Γ (Skels.app ss (.pi A' B')) (Skels.app ss (.sort (.imax u v)))}
    (ha : hA.AssumpPref) (hbap : hB.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvPi ss A A' B B' u v hA hB dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨ha, hbap, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvLetE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (A A' v v' b b' B : Expr Nat) (u : Level)
    {hA : CvP E n Γ (Skels.app ss A) (Skels.app ss A')
      (.sort (Skels.appLevel ss u))}
    {hv : CvP E n Γ (Skels.app ss v) (Skels.app ss v') (Skels.app ss A)}
    {hb : CvP E n (.letBinding (Skels.app ss A) (Skels.app ss v) :: Γ)
      (Skels.app (ss.map Skel.shift) b) (Skels.app (ss.map Skel.shift) b')
      (Skels.app (ss.map Skel.shift) B)}
    {dl : TyP E n Γ (Skels.app ss (.letE A v b)) (Skels.app ss (instantiate0 v B))}
    {dr : TyP E n Γ (Skels.app ss (.letE A' v' b'))
      (Skels.app ss (instantiate0 v B))}
    (ha : hA.AssumpPref) (hvap : hv.AssumpPref) (hbap : hb.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvLetE ss A A' v v' b b' B u hA hv hb dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨ha, hvap, hbap, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvSorts {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (l₁ l₂ : Level) (h : eqN l₁ l₂)
    {dl : TyP E n Γ (Skels.app ss (.sort l₁)) (Skels.app ss (.sort (.succ l₁)))}
    {dr : TyP E n Γ (Skels.app ss (.sort l₂)) (Skels.app ss (.sort (.succ l₁)))}
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvSorts ss l₁ l₂ h dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvConsts {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : CvWalkHyp E) (ss : List (PStep E n)) (nIn : Nat) (hfuel : FuelRel ss nIn)
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded nIn ls = true) (hwf' : levelsBounded nIn ls' = true)
    (h : eqNList ls ls')
    {dl : TyP E n Γ (Skels.app (steps ss) (.const r ls))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))}
    {dr : TyP E n Γ (Skels.app (steps ss) (.const r ls'))
      (Skels.app (steps ss) (instantiateLevels ls m.mtype))}
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvConsts hW ss nIn hfuel hres hlen hwf hwf' h dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvEta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (f A B : Expr Nat)
    {h : TyP E n Γ (Skels.app ss f) (Skels.app ss (.pi A B))}
    {dl : TyP E n Γ (Skels.app ss (.lam A (.app (lift 0 1 f) (.bvar 0))))
      (Skels.app ss (.pi A B))}
    {dr : TyP E n Γ (Skels.app ss f) (Skels.app ss (.pi A B))}
    (hap : h.AssumpPref) (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvEta ss f A B h dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨?_, ?_, ?_⟩
  · exact assumpPref_toPi hap
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

theorem assumpPref_cvIrr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (P pv q : Expr Nat)
    {hP : TyP E n Γ (Skels.app ss P) (Skels.app ss (.sort .zero))}
    {hp : TyP E n Γ (Skels.app ss pv) (Skels.app ss P)}
    {hq : TyP E n Γ (Skels.app ss q) (Skels.app ss P)}
    {dl : TyP E n Γ (Skels.app ss pv) (Skels.app ss P)}
    {dr : TyP E n Γ (Skels.app ss q) (Skels.app ss P)}
    (hPap : hP.AssumpPref) (hpap : hp.AssumpPref) (hqap : hq.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvIrr ss P pv q hP hp hq dl dr).AssumpPref := by
  refine ⟨?_, hpap, hqap, hdl, hdr⟩
  exact assumpPref_toSortZero hPap

theorem assumpPref_cvFsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ss : List Skel) (A B S a b : Expr Nat) (u : Level)
    {hB : TyP E n (.assumption (Skels.app ss A) :: Γ)
      (Skels.app (ss.map Skel.shift) B) (Skels.app (ss.map Skel.shift) S)}
    {hA : TyP E n Γ (Skels.app ss A) (.sort (Skels.appLevel ss u))}
    {hab : CvP E n Γ (Skels.app ss a) (Skels.app ss b) (Skels.app ss A)}
    {dl : TyP E n Γ (Skels.app ss (instantiate0 a B))
      (Skels.app ss (instantiate0 a S))}
    {dr : TyP E n Γ (Skels.app ss (instantiate0 b B))
      (Skels.app ss (instantiate0 a S))}
    (hBap : hB.AssumpPref) (hAap : hA.AssumpPref) (habap : hab.AssumpPref)
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref) :
    (cvFsub ss A B S a b u hB hA hab dl dr).AssumpPref := by
  refine assumpPref_cvCast _ _ _ ?_
  refine ⟨hBap, hAap, habap, ?_, ?_⟩
  · exact assumpPref_tyCast _ _ hdl
  · exact assumpPref_tyCast _ _ hdr

/-! ## §9 the walk preserves `AssumpPref` -/

set_option maxHeartbeats 800000
mutual

/-- `tyAtLet` preserves `AssumpPref`: every emitted transport is a cutoff-0
    `wk` from `wkFront`/`cvFront`, and every carried payload is tracked by
    `packLAP`. -/
theorem tyAtLet_ap {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E) :
    ∀ {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat}
      {uSlot : Level} {ss : List (PStep E n)} {e T : Expr Nat}
      {D : TyP Ei nIn Γ e T}
      {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ},
      packLAP p → D.AssumpPref → (tyAtLet hW ι ιenv hext p D).AssumpPref
  | _, _, _, _, _, _, _, _, ss, _, _, .sort _ _ _ l k' h, _, _, _ =>
      assumpPref_tySort l k' h (steps ss)
  | _, _, k, _, _, Dom', Val', _, ss, _, _,
      .bvar _ _ Γ0 i A _ hlu hA, p, hp, hD =>
      assumpPref_finishBvarL p.get hp.2.1
        (assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hD))
        (bwalkAtL_ap k Dom' Val' ss i A Γ0 hlu p.inv p.run hp.1)
  | _, _, _, _, _, _, _, _, ss, _, _,
      .const _ _ _ r ls ls₀ m _ hres hlen hwf hls hT, p, hp, hD =>
      assumpPref_tyConst hW (hext r m hres) hlen hwf hls ss p.fuel
        (assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hT) hD))
  | _, _, _, _, _, _, _, _, ss, _, _, .pi _ _ _ A u B v hA hB, p, hp, hD => by
      refine assumpPref_tyPi A B u v (steps ss) ?_ ?_
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hD.1)
      · exact assumpPref_toSort (assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (D := hB) hD.2))
  | _, _, _, _, _, _, _, _, ss, _, _,
      .lam _ _ _ A u body B v hA hbody hB, p, hp, hD => by
      refine assumpPref_tyLam A body B u v (steps ss) ?_ ?_ ?_
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hD.1)
      · exact assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (D := hbody) hD.2.1)
      · exact assumpPref_toSort (assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (D := hB) hD.2.2))
  | _, _, _, _, _, _, _, _, ss, _, _,
      .app _ _ _ f a A B w hf ha hT, p, hp, hD => by
      refine assumpPref_tyApp f a A B w (steps ss) ?_ ?_ ?_
      · exact assumpPref_toPi (tyAtLet_ap hW ι ιenv hext hp (D := hf) hD.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := ha) hD.2.1
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hT) hD.2.2)
  | _, _, _, _, _, _, _, _, ss, _, _,
      .letE _ _ _ A u value B body w hA hv hb hT, p, hp, hD => by
      refine assumpPref_tyLet A value B body u w (steps ss) ?_ ?_ ?_ ?_
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hD.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := hv) hD.2.1
      · exact assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.letBinding A value)
              (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
              (onDecl_let (steps ss) A value).symm hp)
            (D := hb) hD.2.2.1)
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hT) hD.2.2.2)
  | _, _, _, _, _, _, _, _, ss, _, T, .lit _ _ _ t _ hexp, _, hp, hD =>
      assumpPref_tyLit t T (steps ss) (tyAtLet_ap hW ι ιenv hext hp (D := hexp) hD)
  | _, _, _, _, _, _, _, _, ss, _, _, .conv _ _ _ _ _ _ _ h hc, _, hp, hD =>
      ⟨tyAtLet_ap hW ι ιenv hext hp (D := h) hD.1,
        assumpPref_cvToSort (cvAtLet_ap hW ι ιenv hext hp (C := hc) hD.2)⟩
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _,
      .wk _ _ Γ0 e0 A0 d c Di, p, hp, hD =>
      tyAtLet_ap hW ι ιenv hext (packLAP_consWk c d hp) (D := Di) hD.2
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _,
      .esub _ _ Γ0 e0 A0 t v j _ Di hget hv hvT, p, hp, hD =>
      tyAtLet_ap hW ι ιenv hext
        (packLAP_esub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (tyAtLet_ap hW ι ιenv hext hp (D := hv) hD.2.2.1) hp)
        (D := Di) hD.2.1
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _,
      .lsub _ _ Γ0 e0 A0 t v j _ Di hget hv hvT, p, hp, hD =>
      tyAtLet_ap hW ι ιenv hext
        (packLAP_lsub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (tyAtLet_ap hW ι ιenv hext hp (D := hv) hD.2.2.1) hp)
        (D := Di) hD.2.1
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _,
      .linst _ a nIn Γ0 e0 A0 ls hls hlen Di, p, hp, hD =>
      tyAtLet_ap hW ι ιenv hext (packLAP_linst ls a nIn hls hlen hp) (D := Di) hD
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _,
      .ewk E₀ _ _ _ _ _ hext' Di, p, hp, hD =>
      tyAtLet_ap hW ι ιenv (envExt_trans hext' hext) hp (D := Di) hD
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _,
      .cctx _ _ Γ0 e0 T0 A A' _ Dinner hA, p, hp, hD => by
      let hc0 := cvAtLet hW ι ιenv hext (packLWk (.assumption A') p) hA
      have hd := cvAtLet_ap hW ι ιenv hext (packLAP_wk (.assumption A') hp)
        (C := hA) hD.2
      let flipped := CvP.symm E n
        (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ0)))
        (Skels.app (steps ss) (lift 0 1 A))
        (Skels.app (steps ss) (lift 0 1 A'))
        (.sort (Skels.appLevel (steps ss) _))
        (cvToSort hc0) (toSort hc0.dr) (toSort hc0.dl)
      refine tyAtLet_ap hW ι ιenv hext
        (packLAP_cctx (hc := flipped) ?_ hp) (D := Dinner) hD.1
      · refine ⟨?_, ?_, ?_⟩
        · exact assumpPref_cvToSort hd
        · exact assumpPref_toSort (assumpPref_dr hd)
        · exact assumpPref_toSort (assumpPref_dl hd)

/-- `cvAtLet` preserves `AssumpPref`. -/
theorem cvAtLet_ap {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E) :
    ∀ {nIn : Nat} {Γ : LCtx} {k : Nat} {Dom Val Dom' Val' : Expr Nat}
      {uSlot : Level} {ss : List (PStep E n)} {a b T : Expr Nat}
      {C : CvP Ei nIn Γ a b T}
      {p : PackL E n k Dom Val Dom' Val' uSlot nIn ss Γ},
      packLAP p → C.AssumpPref → (cvAtLet hW ι ιenv hext p C).AssumpPref
  | _, _, _, _, _, _, _, _, ss, _, _, _, .refl _ _ _ a A h dl dr, p, hp, hC =>
      ⟨tyAtLet_ap hW ι ιenv hext hp (D := h) hC.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2⟩
  | _, _, _, _, _, _, _, _, ss, _, _, _, .symm _ _ _ a b A h dl dr, p, hp, hC =>
      ⟨cvAtLet_ap hW ι ιenv hext hp (C := h) hC.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2⟩
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .trans _ _ _ a b c A h1 h2 dl dr, p, hp, hC =>
      ⟨cvAtLet_ap hW ι ιenv hext hp (C := h1) hC.1,
        cvAtLet_ap hW ι ιenv hext hp (C := h2) hC.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2⟩
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .beta _ _ _ A body arg B u hA hbody harg dl dr, p, hp, hC => by
      refine assumpPref_cvBeta (steps ss) A body arg B u ?_ ?_ ?_ ?_ ?_
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hC.1)
      · exact assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (D := hbody) hC.2.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := harg) hC.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .zeta _ _ _ A value body B u hA hv hb dl dr, p, hp, hC => by
      refine assumpPref_cvZeta (steps ss) A value body B u ?_ ?_ ?_ ?_ ?_
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hC.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := hv) hC.2.1
      · exact assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.letBinding A value)
              (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) value))
              (onDecl_let (steps ss) A value).symm hp)
            (D := hb) hC.2.2.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2.2
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _, _,
      .zetaLocal _ _ _ i vA val hval hty hv dl dr, p, hp, hC => by
      simp only [cvAtLet]
      split
      · rename_i hterm
        refine assumpPref_cvCast _ _ _ ?_
        refine ⟨?_, ?_, ?_⟩
        · exact tyAtLet_ap hW ι ιenv hext hp (D := hv) hC.1
        · exact assumpPref_tyCast _ _ (tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1)
        · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2
      · rename_i j hterm hvl hlk
        split
        · refine assumpPref_cvCast _ _ _ ?_
          exact assumpPref_retypeLetBValSlot hp.2.1 hp.2.2 p.get
        · refine assumpPref_cvCast _ _ _ ?_
          refine ⟨?_, ?_, ?_⟩
          · exact tyAtLet_ap hW ι ιenv hext hp (D := hv) hC.1
          · exact assumpPref_tyCast _ _ (tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1)
          · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .delta _ nIn _ r ls m b hres hbody htr hlen hwf hb dl dr, p, hp, hC => by
      refine assumpPref_cvDelta hW ss nIn p.fuel (hext r m hres) hbody htr hlen
        hwf ?_ ?_ ?_
      · exact tyAtLet_ap hW ι ιenv hext hp (D := hb) hC.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .iota _ _ _ lhs rhs _ h hlhs hrhs dl dr, p, hp, hC =>
      ⟨tyAtLet_ap hW ι ιenv hext hp (D := hlhs) hC.1,
        tyAtLet_ap hW ι ιenv hext hp (D := hrhs) hC.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2⟩
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .lit _ _ _ t _ _ (.of _) hexp dl dr, p, hp, hC =>
      assumpPref_cvLit (steps ss) t _
        (tyAtLet_ap hW ι ιenv hext hp (D := hexp) hC.1)
        (tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1)
        (tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2)
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .app _ _ _ f g a b A B h1 h2 dl dr, p, hp, hC => by
      refine assumpPref_cvApp (steps ss) f g a b A B ?_ ?_ ?_ ?_
      · exact cvAtLet_ap hW ι ιenv hext hp (C := h1) hC.1
      · exact cvAtLet_ap hW ι ιenv hext hp (C := h2) hC.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .lam _ _ _ A A' b b' B u hA hb dl dr, p, hp, hC => by
      refine assumpPref_cvLam (steps ss) A A' b b' B u ?_ ?_ ?_ ?_
      · exact assumpPref_cvToSort (cvAtLet_ap hW ι ιenv hext hp (C := hA) hC.1)
      · exact assumpPref_moveUnderCvL _
          (cvAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (C := hb) hC.2.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .pi _ _ _ A A' B B' u v hA hB dl dr, p, hp, hC => by
      refine assumpPref_cvPi (steps ss) A A' B B' u v ?_ ?_ ?_ ?_
      · exact assumpPref_cvToSort (cvAtLet_ap hW ι ιenv hext hp (C := hA) hC.1)
      · exact assumpPref_cvToSort (assumpPref_moveUnderCvL _
          (cvAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (C := hB) hC.2.1))
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .letE _ _ _ A A' v v' b b' B u hA hv hb dl dr, p, hp, hC => by
      refine assumpPref_cvLetE (steps ss) A A' v v' b b' B u ?_ ?_ ?_ ?_ ?_
      · exact assumpPref_cvToSort (cvAtLet_ap hW ι ιenv hext hp (C := hA) hC.1)
      · exact cvAtLet_ap hW ι ιenv hext hp (C := hv) hC.2.1
      · exact assumpPref_moveUnderCvL _
          (cvAtLet_ap hW ι ιenv hext
            (packLAP_under (.letBinding A v)
              (.letBinding (Skels.app (steps ss) A) (Skels.app (steps ss) v))
              (onDecl_let (steps ss) A v).symm hp)
            (C := hb) hC.2.2.1)
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .sorts _ _ _ l₁ l₂ h dl dr, p, hp, hC => by
      refine assumpPref_cvSorts (steps ss) l₁ l₂ h ?_ ?_
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .consts _ nIn _ r ls ls' m hres hlen hwf hwf' h dl dr, p, hp, hC => by
      refine assumpPref_cvConsts hW ss nIn p.fuel (hext r m hres) hlen hwf hwf'
        h ?_ ?_
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .eta _ _ _ f A B h dl dr, p, hp, hC => by
      refine assumpPref_cvEta (steps ss) f A B ?_ ?_ ?_
      · exact tyAtLet_ap hW ι ιenv hext hp (D := h) hC.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .irr _ _ _ P pv q hP hpv hq dl dr, p, hp, hC => by
      refine assumpPref_cvIrr (steps ss) P pv q ?_ ?_ ?_ ?_ ?_
      · exact tyAtLet_ap hW ι ιenv hext hp (D := hP) hC.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := hpv) hC.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := hq) hC.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2.2
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .tyConv _ _ _ a b A B u h hA dl dr, p, hp, hC =>
      ⟨cvAtLet_ap hW ι ιenv hext hp (C := h) hC.1,
        assumpPref_cvToSort (cvAtLet_ap hW ι ιenv hext hp (C := hA) hC.2.1),
        tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.1,
        tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2⟩
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _, _,
      .wk _ _ Γ0 a0 b0 T0 d c h, p, hp, hC =>
      cvAtLet_ap hW ι ιenv hext (packLAP_consWk c d hp) (C := h) hC.2
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _, _,
      .esub _ _ Γ0 a0 b0 T0 t v j _ h hget hv hvT, p, hp, hC =>
      cvAtLet_ap hW ι ιenv hext
        (packLAP_esub ((List.get?_eq_getElem? Γ0 j).symm ▸ hget)
          (tyAtLet_ap hW ι ιenv hext hp (D := hv) hC.2.2.1) hp)
        (C := h) hC.2.1
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _, _,
      .linst _ a nIn Γ0 a0 b0 T0 ls hls hlen h, p, hp, hC =>
      cvAtLet_ap hW ι ιenv hext (packLAP_linst ls a nIn hls hlen hp) (C := h) hC
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _, _,
      .ewk E₀ _ _ _ _ _ _ hext' h, p, hp, hC =>
      cvAtLet_ap hW ι ιenv (envExt_trans hext' hext) hp (C := h) hC
  | _, _, k, Dom, Val, Dom', Val', uSlot, ss, _, _, _,
      .cctx _ _ Γ0 a0 b0 T0 A A' _ h hA, p, hp, hC => by
      let hc0 := cvAtLet hW ι ιenv hext (packLWk (.assumption A') p) hA
      have hd := cvAtLet_ap hW ι ιenv hext (packLAP_wk (.assumption A') hp)
        (C := hA) hC.2
      let flipped := CvP.symm E n
        (setLetB k Dom' Val' (Skels.ctx (steps ss) (.assumption A' :: Γ0)))
        (Skels.app (steps ss) (lift 0 1 A))
        (Skels.app (steps ss) (lift 0 1 A'))
        (.sort (Skels.appLevel (steps ss) _))
        (cvToSort hc0) (toSort hc0.dr) (toSort hc0.dl)
      refine cvAtLet_ap hW ι ιenv hext
        (packLAP_cctx (hc := flipped) ?_ hp) (C := h) hC.1
      · refine ⟨?_, ?_, ?_⟩
        · exact assumpPref_cvToSort hd
        · exact assumpPref_toSort (assumpPref_dr hd)
        · exact assumpPref_toSort (assumpPref_dl hd)
  | _, _, _, _, _, _, _, _, ss, _, _, _,
      .fsub _ _ _ A B S a b u hB hA hab dl dr, p, hp, hC => by
      refine assumpPref_cvFsub (steps ss) A B S a b u ?_ ?_ ?_ ?_ ?_
      · exact assumpPref_moveUnderL _
          (tyAtLet_ap hW ι ιenv hext
            (packLAP_under (.assumption A) (.assumption (Skels.app (steps ss) A))
              (onDecl_assumption (steps ss) A).symm hp)
            (D := hB) hC.1)
      · exact assumpPref_toSort (tyAtLet_ap hW ι ιenv hext hp (D := hA) hC.2.1)
      · exact cvAtLet_ap hW ι ιenv hext hp (C := hab) hC.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dl) hC.2.2.2.1
      · exact tyAtLet_ap hW ι ιenv hext hp (D := dr) hC.2.2.2.2

end

/-! ## §10 the `LetCtxConvP.AssumpPref` contract (Q7 totality) -/

/-- The `letCtxConvP_of_cvWalkHyp`-discharged `LetCtxConvP` satisfies the
    `AssumpPref` contract: at `k = 0` the pack is `packNilL` (empty skeleton —
    `pStepsAP []` is trivial — and slot conversions `hA`/`hv` themselves), so
    `tyAtLet_ap` applies directly. -/
theorem letCtxConvP_ap {E : ResolvedEnv} (w : CvWalkHyp E) {n : Nat} :
    LetCtxConvP.AssumpPref (letCtxConvP_of_cvWalkHyp w (n := n)) :=
  fun {Γ A A' v v' e T u} {hA : CvP E n Γ A A' (.sort u)}
      {hv : CvP E n Γ v v' A} {D : TyP E n (.letBinding A v :: Γ) e T}
      (hapA : hA.AssumpPref) (hapv : hv.AssumpPref) (hD : D.AssumpPref) =>
    tyAtLet_ap w (iotaPack_of_cvWalkHyp w)
      (fun hext' h => derivedIotaExt hext' h) (envExt_refl E)
      (p := packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 =
        some (.letBinding A v)) hA hv)
      (packLAP_nil hapA hapv) hD

end Rcic.Syn

#print axioms Rcic.Syn.tyAtLet_ap
#print axioms Rcic.Syn.cvAtLet_ap
#print axioms Rcic.Syn.letCtxConvP_ap
