import rcic.RcicSynLetRight

/-!
# BelowC mixed interpreter, part 2 — §8 the `U` right-surface worker

`research/rcic/sortrow/BELOWC_MIXED_INTERPRETER.md` §8 (docs PR #7477), compiled against the
landed Wall 2 LetBridge (`RcicSynLetRight`, #7452).

The LetBridge record `LetBridgeAnswers` has one input that is not a smaller answer of the
original tree: `rightSurface : U.eps μ ρ ≈ dr.eps μ ρ`, the MixedCL of the un-inlined let
`U := letRightSurface …` against the original right endpoint `dr`. §8 gives its recursive
reduction at the **direct stage**: the peer of `U` is decoded to a native let
`R = TyP.letE gA gv gb gT` (wrappers, `conv`, `ewk`, `cctx` have identity erasure, so forward
decoding yields the equation `dr.eps μ ρ = R.eps μ ρ`), and the worker issues

* `q_V = MCL/Tag[hv.dr, gv]` at the exterior stage — `Rel tbl (hv.dr.eps μ ρ) (gv.eps μ ρ)`;
* `q_B = MCL[hb.dr at δ_L, gb at δ_g]` — the original right body under the *left* let display
  `δ_L = letDisp (hv.dl.eps μ ρ) :: ρ` against the peer body under its own display
  `δ_g = letDisp (gv.eps μ ρ) :: ρ` (the `changedLet` correspondence; ascriptions may differ).

The finish is `e[U] = e[D'; δ_R]` (`eps_letRightSurface`), `H_bridge⁻¹` (the unary LetBridge
induction `letBridge`, read backwards), then `q_B`, then the decoded peer:
`e[U] = e[D'; δ_R] ≈ e[hb.dr; δ_L] ≈ e[gb; δ_g] = e[R] = e[dr]`. `q_V` is consumed at an inline
use inside `q_B`'s worker: the provider relation `Rel(e[hv.dl], e[gv])` is `ES[hv]` with its two
PBs (`Rel(e[hv.dl], e[hv.dr])`) composed with `q_V`.

Precision notes. (1) `hdr` is the outcome of forward decoding, stated as the erasure equation it
yields; when `dr` is the native let itself it is `rfl`. (2) At the direct stage `q_B` and the
`hR` goal of `es_of_below_letE_of_dr` are inter-derivable through `let_eps_eq`; the bridge is
what the `U` *view* costs (the worker is born on `MCL[U, dr]`, §3 "LetBridge right surface"),
not what `hR` costs. No lemma here restates `hR` from `q_B`. (3) Never `Reg U`, never
`MEUT U _`: only `U.eps` appears, through `eps_letRightSurface`.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the initial value relation from `ES[hv]` and its two PBs -/

/-- `Rel(e[hv.dl], e[hv.dr])` from exactly `ES[hv]`, `PB[hv.dl, hA.dl]`, `PB[hv.dr, hA.dl]`
    (the construction inside `rel_value_of_answers`, available before the record is complete). -/
theorem rel_value_of_es_pb {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    {Γ : LCtx} {A A' v v' : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A} {μ : Level → Level} {ρ : List Disp}
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ))
    (valuePBLeft : PBit μ ρ hv.dl hA.dl) (valuePBRight : PBit μ ρ hv.dr hA.dl) :
    Rel tbl (hv.dl.eps μ ρ) (hv.dr.eps μ ρ) :=
  ⟨valueES, valuePBLeft.trans valuePBRight.symm⟩

/-! ## §2 the worker's two requests at the direct stage -/

/-- The `U` right-surface worker's requests (§8) once the peer is decoded to the native let
    `TyP.letE gA gv gb gT` displaying `letE A' v' b'`. -/
structure USurfaceRequests {E : ResolvedEnv} {n : Nat} (tbl : List CRule)
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat}
    (hv : CvP E n Γ v v' A) (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    {B' : Expr Nat} (gv : TyP E n Γ v' A') (gb : TyP E n (.letBinding A' v' :: Γ) b' B')
    (μ : Level → Level) (ρ : List Disp) : Prop where
  /-- `q_V = MCL/Tag[hv.dr, gv]` at the exterior stage. -/
  valueRel : Rel tbl (hv.dr.eps μ ρ) (gv.eps μ ρ)
  /-- `q_B = MCL[hb.dr at δ_L, gb at δ_g]`: the original right body under the left let display
      against the peer body under its own display. -/
  bodyCL : ConvMod (EStep tbl) LvlEq
    (hb.dr.eps μ (letDisp (hv.dl.eps μ ρ) :: ρ)) (gb.eps μ (letDisp (gv.eps μ ρ) :: ρ))

/-- §8, inline use: the provider worker's relation `Rel(e[hv.dl], e[gv])` — `ES[hv]` with its
    two PBs, then `q_V` (strict provider calls). -/
theorem rel_value_peer {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb : CvP E n (.letBinding A v :: Γ) b b' B}
    {B' : Expr Nat} {gv : TyP E n Γ v' A'} {gb : TyP E n (.letBinding A' v' :: Γ) b' B'}
    {μ : Level → Level} {ρ : List Disp}
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ))
    (valuePBLeft : PBit μ ρ hv.dl hA.dl) (valuePBRight : PBit μ ρ hv.dr hA.dl)
    (q : USurfaceRequests tbl hv hb gv gb μ ρ) :
    Rel tbl (hv.dl.eps μ ρ) (gv.eps μ ρ) :=
  (rel_value_of_es_pb valueES valuePBLeft valuePBRight).trans q.valueRel

/-- §8, inline use: the two body stages `δ_L` / `δ_g` are display-related entrywise. -/
theorem dispRel_peer {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb : CvP E n (.letBinding A v :: Γ) b b' B}
    {B' : Expr Nat} {gv : TyP E n Γ v' A'} {gb : TyP E n (.letBinding A' v' :: Γ) b' B'}
    {μ : Level → Level} {ρ : List Disp}
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ))
    (valuePBLeft : PBit μ ρ hv.dl hA.dl) (valuePBRight : PBit μ ρ hv.dr hA.dl)
    (q : USurfaceRequests tbl hv hb gv gb μ ρ) :
    DispRel tbl (letDisp (hv.dl.eps μ ρ) :: ρ) (letDisp (gv.eps μ ρ) :: ρ) :=
  DispRel.letDisp (rel_value_peer valueES valuePBLeft valuePBRight q) (DispRel.refl tbl ρ)

/-! ## §3 the finish: `rightSurface` from `H_bridge⁻¹`, `q_B` and the decoded peer -/

/-- §8 finish against the native peer let itself: `e[U] = e[D'; δ_R]` (`eps_letRightSurface`),
    `H_bridge⁻¹` (the unary LetBridge at the empty stack, read right-to-left), then `q_B`
    (`let_eps_eq` on the peer). The bridge consumes exactly the record's smaller answers:
    `ES[hv]`, the two value PBs and the per-node `BodyAnswers` at the root stage. Only `q_B` is
    consumed here; `q_V` is consumed inside `q_B`'s worker (`rel_value_peer`). -/
theorem rightSurface_of_bodyCL {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    (hcl : TableClosed tbl) (w : CvWalkHyp E) {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (μ : Level → Level) (ρ : List Disp)
    (hAP : hb.dr.AssumpPref) (hfit : DisplayFits Γ ρ)
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ))
    (valuePBLeft : PBit μ ρ hv.dl hA.dl) (valuePBRight : PBit μ ρ hv.dr hA.dl)
    (body : BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl μ
      (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps μ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps μ ρ) :: ρ))
    {u' w' : Level} {B' : Expr Nat}
    (gA : TyP E n Γ A' (.sort u')) (gv : TyP E n Γ v' A')
    (gb : TyP E n (.letBinding A' v' :: Γ) b' B') (gT : TyP E n Γ (instantiate0 v' B') (.sort w'))
    (bodyCL : ConvMod (EStep tbl) LvlEq
      (hb.dr.eps μ (letDisp (hv.dl.eps μ ρ) :: ρ)) (gb.eps μ (letDisp (gv.eps μ ρ) :: ρ))) :
    ConvMod (EStep tbl) LvlEq
      ((letRightSurface w hA hv hb.dr hb.dr.reg.1 hb.dr.reg.2).eps μ ρ)
      ((TyP.letE E n Γ A' u' v' B' b' w' gA gv gb gT).eps μ ρ) := by
  rw [eps_letRightSurface, let_eps_eq]
  have hdisp : DispRel tbl (letDisp (hv.dl.eps μ ρ) :: ρ) (letDisp (hv.dr.eps μ ρ) :: ρ) :=
    DispRel.letDisp (rel_value_of_es_pb valueES valuePBLeft valuePBRight) (DispRel.refl tbl ρ)
  have htr := traceInv_nil (μ' := μ) (E := E) (n := n) (k := 0) (Dom' := A') (Val' := v')
    (Γ := .letBinding A v :: Γ) hcl hdisp
  have hbridge := letBridge hcl w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h)
    μ (envExt_refl E) hb.dr
    (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
    (letDisp (hv.dl.eps μ ρ) :: ρ) [] .nil
    (letDisp (hv.dr.eps μ ρ) :: ρ) hAP (displayFits_letDisp A v _ hfit) trivial htr body
  exact (ConvMod.symm' LvlEq.symm' hbridge.conv).trans bodyCL

/-- §8 finish at a decoded peer: `hdr` is the outcome of forward decoding (`dr.eps μ ρ` equals the
    native peer's erasure), then `rightSurface_of_bodyCL` with the record's `q_B`. -/
theorem rightSurface_of_requests {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    (hcl : TableClosed tbl) (w : CvWalkHyp E) {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (μ : Level → Level) (ρ : List Disp)
    (hAP : hb.dr.AssumpPref) (hfit : DisplayFits Γ ρ)
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ))
    (valuePBLeft : PBit μ ρ hv.dl hA.dl) (valuePBRight : PBit μ ρ hv.dr hA.dl)
    (body : BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl μ
      (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps μ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps μ ρ) :: ρ))
    {u' w' : Level} {B' : Expr Nat}
    (gA : TyP E n Γ A' (.sort u')) (gv : TyP E n Γ v' A')
    (gb : TyP E n (.letBinding A' v' :: Γ) b' B') (gT : TyP E n Γ (instantiate0 v' B') (.sort w'))
    (hdr : dr.eps μ ρ = (TyP.letE E n Γ A' u' v' B' b' w' gA gv gb gT).eps μ ρ)
    (q : USurfaceRequests tbl hv hb gv gb μ ρ) :
    ConvMod (EStep tbl) LvlEq
      ((letRightSurface w hA hv hb.dr hb.dr.reg.1 hb.dr.reg.2).eps μ ρ) (dr.eps μ ρ) := by
  rw [hdr]
  exact rightSurface_of_bodyCL hcl w hA hv hb μ ρ hAP hfit valueES valuePBLeft valuePBRight body
    gA gv gb gT q.bodyCL

/-- §8: the complete `LetBridgeAnswers` from the smaller answers and the worker's requests —
    the `rightSurface` input discharged by `rightSurface_of_requests`. -/
theorem letBridgeAnswers_of_requests {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    (hcl : TableClosed tbl) (w : CvWalkHyp E) {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (μ : Level → Level) (ρ : List Disp)
    (hAP : hb.dr.AssumpPref) (hfit : DisplayFits Γ ρ)
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ))
    (valuePBLeft : PBit μ ρ hv.dl hA.dl) (valuePBRight : PBit μ ρ hv.dr hA.dl)
    (body : BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl μ
      (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps μ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps μ ρ) :: ρ))
    {u' w' : Level} {B' : Expr Nat}
    (gA : TyP E n Γ A' (.sort u')) (gv : TyP E n Γ v' A')
    (gb : TyP E n (.letBinding A' v' :: Γ) b' B') (gT : TyP E n Γ (instantiate0 v' B') (.sort w'))
    (hdr : dr.eps μ ρ = (TyP.letE E n Γ A' u' v' B' b' w' gA gv gb gT).eps μ ρ)
    (q : USurfaceRequests tbl hv hb gv gb μ ρ) :
    LetBridgeAnswers tbl w hA hv hb dr μ ρ :=
  ⟨valueES, valuePBLeft, valuePBRight, body,
    rightSurface_of_requests hcl w hA hv hb dr μ ρ hAP hfit valueES valuePBLeft valuePBRight body
      gA gv gb gT hdr q⟩

/-- §8 applied: the `ES` arm for `CvP.letE` from the smaller answers and the `U` worker's two
    requests at the direct stage (`es_of_below_letE_of_letBridge` with its record built here). -/
theorem es_of_below_letE_of_requests (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {tbl : List CRule} (hcl : TableClosed tbl) (w : CvWalkHyp E) {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)))
    (hAP : hb.dr.AssumpPref)
    (valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps σ ρ) (hv.dr.eps σ ρ))
    (valuePBLeft : PBit σ ρ hv.dl hA.dl) (valuePBRight : PBit σ ρ hv.dr hA.dl)
    (body : BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl σ
      (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps σ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps σ ρ) :: ρ))
    {u' w' : Level} {B' : Expr Nat}
    (gA : TyP E n Γ A' (.sort u')) (gv : TyP E n Γ v' A')
    (gb : TyP E n (.letBinding A' v' :: Γ) b' B') (gT : TyP E n Γ (instantiate0 v' B') (.sort w'))
    (hdr : dr.eps σ ρ = (TyP.letE E n Γ A' u' v' B' b' w' gA gv gb gT).eps σ ρ)
    (q : USurfaceRequests tbl hv hb gv gb σ ρ) :
    ES tbl σ ρ (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) :=
  es_of_below_letE_of_letBridge Aw hcl w hA hv hb dl dr σ ρ hρ Bel hAP
    (letBridgeAnswers_of_requests hcl w hA hv hb dr σ ρ hAP
      (DisplayFits.of_dispShape (dispShape_of_dispFor hρ)) valueES valuePBLeft valuePBRight body
      gA gv gb gT hdr q)

end Rcic.Syn

#print axioms Rcic.Syn.rel_value_of_es_pb
#print axioms Rcic.Syn.USurfaceRequests
#print axioms Rcic.Syn.rel_value_peer
#print axioms Rcic.Syn.dispRel_peer
#print axioms Rcic.Syn.rightSurface_of_bodyCL
#print axioms Rcic.Syn.rightSurface_of_requests
#print axioms Rcic.Syn.letBridgeAnswers_of_requests
#print axioms Rcic.Syn.es_of_below_letE_of_requests
