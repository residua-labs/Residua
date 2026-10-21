import rcic.RcicSynInstEnd
import rcic.RcicERPiSlot
import rcic.RcicSynSortRow
import rcic.RcicSynInst
import rcic.RcicSynBvarEsub
import rcic.RcicERLocalize

/-!
# Syntactic sortRow, BelowC mixed step — `RcicSynMixedFinish2`

Part I §3–§4 of `research/rcic/sortrow/BELOWC_MIXED_STEP_AND_LEDGER.md`
(docs PR #7455, branch `docs/belowc-mixed-ledger`).

§3.1  the `instEnd`/`piSlot` identity `e[instEnd(hB,ha,hA)] = inst 0 a_E (piSlot b q)`
      for both bits `b` (`instEnd_eps_keep`/`instEnd_eps_drop` + `piSlot_inst_id`);
§3.2  `mixedEUT_app_uniform_finish` — the padded-codomain application composition
      that removes the domain-bit alignment premise (Π-injectivity across the two
      padded codomains, each `inst 0` at its own erased argument);
§3.3  the two pending-outer-action equations through `inst 0 a p`
      (`lift`/`inst` commute);
§4.1/§4.2 the one-hit and two-hit MEUT compositions as finite `ConvMod` chains,
      with the spec's exact orientations;
§4.3  the term-erasure hit equation `e[τD] = e[V]` for `esub` and R2 `lsub`,
      with `PB[V,W]`, the `G/W` gate and same-stage scope as explicit hypotheses.

Hypotheses only — no supplier side; `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §3.1 `e[instEnd]` through the `piSlot` pad

The `b`-selected binder display is `binderDisp b :: ρ` — the landed
`binderDisp : Bool → Disp` (`RcicSynPack`: `true ↦ drop`, `false ↦ keep`). -/

/-- §3.1, `b = false`: `instEnd_eps_keep` already gives the `inst 0` form and
    `piSlot false` is the identity. -/
theorem instEnd_eps_piSlot_false {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) :
    (instEnd hB hv hA).eps σ ρ =
      ETm.inst 0 (hv.eps σ ρ) (piSlot false (hB.eps σ (.keep :: ρ))) :=
  instEnd_eps_keep hB hv hA hu

/-- §3.1, `b = true`: `instEnd_eps_drop` gives `q`, and `piSlot_inst_id` folds the
    `inst 0` into the padded slot (`inst 0 r (q.lift 0 1) = q`). -/
theorem instEnd_eps_piSlot_true {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) :
    (instEnd hB hv hA).eps σ ρ =
      ETm.inst 0 (hv.eps σ ρ) (piSlot true (hB.eps σ (.drop :: ρ))) := by
  rw [instEnd_eps_drop hB hv hA hu]
  exact (piSlot_inst_id _ _).symm

/-- §3.1, both bits: `e[instEnd(hB,ha,hA)] = inst 0 a_E (piSlot b q)` with `q` the
    body erasure at the `b`-selected binder display. Arbitrary `a_E`: no PB, no
    agreement with any other side's bit. -/
theorem instEnd_eps_piSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp} :
    (instEnd hB hv hA).eps σ ρ =
      ETm.inst 0 (hv.eps σ ρ)
        (piSlot (levelIsZero (σ u))
          (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
  cases hb : levelIsZero (σ u) with
  | true => exact instEnd_eps_piSlot_true hB hv hA hb
  | false => exact instEnd_eps_piSlot_false hB hv hA hb

/-! ## §3.2 application EUT without domain-bit alignment -/

/-- §3.2 (term as given): two own-Π views `hPiL`/`hPiR`, the function MEUT `hFun`,
    the argument MCL `hArg`, and the two result-field/instEnd identities
    `hInstL`/`hInstR` compose to `tL ≈ tR`. Π-injectivity compares the padded
    bodies `pL ≈ pR` directly; the argument CL is used even in the double-drop
    branch — `aL`'s `inst 0` into `pR` is what `convMod_inst_repl` supplies. -/
theorem mixedEUT_app_uniform_finish
    {tbl : List CRule} (hW : TableWF tbl)
    {dL dR pL pR rL rR aL aR tL tR : ETm}
    (hPiL : ConvMod (EStep tbl) LvlEq (.pi dL pL) rL)
    (hFun : ConvMod (EStep tbl) LvlEq rL rR)
    (hPiR : ConvMod (EStep tbl) LvlEq rR (.pi dR pR))
    (hArg : ConvMod (EStep tbl) LvlEq aL aR)
    (hInstL : ConvMod (EStep tbl) LvlEq tL (ETm.inst 0 aL pL))
    (hInstR : ConvMod (EStep tbl) LvlEq (ETm.inst 0 aR pR) tR) :
    ConvMod (EStep tbl) LvlEq tL tR := by
  have hBodies : ConvMod (EStep tbl) LvlEq pL pR :=
    (convE_pi_inv_wf hW (hPiL.trans (hFun.trans hPiR))).2
  exact hInstL.trans
    ((convMod_inst_body hW.closed hBodies 0 aL).trans
      ((convMod_inst_repl hW.closed hArg pR 0).trans hInstR))

/-! ## §3.3 pending outer actions through `inst 0` -/

/-- §3.3 lift propagation: `lift c k (inst 0 a p) = inst 0 (lift c k a) (lift (c+1) k p)`.
    The specialization of `ETm.lift_inst_low` at `j = 0`; with `piSlot_lift` this is
    the whole pending-lift clause. -/
theorem lift_inst_zero (c k : Nat) (a p : ETm) :
    (ETm.inst 0 a p).lift c k = ETm.inst 0 (a.lift c k) (p.lift (c + 1) k) :=
  ETm.lift_inst_low k c 0 a (Nat.zero_le c) p

/-- §3.3 inst propagation:
    `inst c r (inst 0 a p) = inst 0 (inst c r a) (inst (c+1) (lift 0 1 r) p)`.
    The specialization of `ETm.inst_inst` at `j = 0`; with `piSlot_inst` this is
    the whole pending-inst clause. -/
theorem inst_inst_zero (c : Nat) (r a p : ETm) :
    ETm.inst c r (ETm.inst 0 a p) =
      ETm.inst 0 (ETm.inst c r a) (ETm.inst (c + 1) (r.lift 0 1) p) :=
  ETm.inst_inst 0 c a r (Nat.zero_le c) p

/-! ## §4.1/§4.2 hit compositions as finite `ConvMod` chains -/

/-- §4.1 one hit: `r[L] ≈ r[ΩV] ≈ e[ΩW] ≈ e[ΩτG] = r[H]` — the packet's own
    `qVal` (`MCL[L, Ω-view(V)]`), `qReg` (`MCL[Ω-view(V.reg), Ω-view(W)]`),
    `qType` (`MCL[Ω∘τ-view(G), Ω-view(W)]`), closed by the §4.3 hit equation
    `hHit : e[ΩτG] = r[H]`. Hypotheses only. -/
theorem mixedEUT_one_hit {tbl : List CRule}
    {rL rΩV eΩW eΩτG rH : ETm}
    (qVal : ConvMod (EStep tbl) LvlEq rL rΩV)
    (qReg : ConvMod (EStep tbl) LvlEq rΩV eΩW)
    (qType : ConvMod (EStep tbl) LvlEq eΩW eΩτG)
    (hHit : eΩτG = rH) :
    ConvMod (EStep tbl) LvlEq rL rH := by
  rw [← hHit]
  exact qVal.trans (qReg.trans qType)

/-- §4.2 both hits: `r[H_L] = e[Ω_L τ_L G_L] ≈ e[Ω_L W_L] ≈ r[Ω_L V_L] ≈ r[Ω_R V_R]
    ≈ e[Ω_R W_R] ≈ e[Ω_R τ_R G_R] = r[H_R]` — left qType forward, left qReg
    backward, central `MEUT[Ω_L V_L, Ω_R V_R]` forward, right qReg forward, right
    qType backward; the two hit equations `hHitL`/`hHitR` are the end brackets.
    Never `MCL[W_L, W_R]`. Hypotheses only. -/
theorem mixedEUT_two_hit {tbl : List CRule}
    {rHL eGL eWL rVL rVR eWR eGR rHR : ETm}
    (hHitL : rHL = eGL)
    (qTypeL : ConvMod (EStep tbl) LvlEq eGL eWL)
    (qRegL : ConvMod (EStep tbl) LvlEq rVL eWL)
    (qMid : ConvMod (EStep tbl) LvlEq rVL rVR)
    (qRegR : ConvMod (EStep tbl) LvlEq rVR eWR)
    (qTypeR : ConvMod (EStep tbl) LvlEq eGR eWR)
    (hHitR : eGR = rHR) :
    ConvMod (EStep tbl) LvlEq rHL rHR := by
  rw [hHitL, ← hHitR]
  exact qTypeL.trans
    ((ConvMod.symm' LvlEq.symm' qRegL).trans
      (qMid.trans (qRegR.trans (ConvMod.symm' LvlEq.symm' qTypeR))))

/-! ## §4.3 the term-erasure hit equation `e[τD] = e[V]` -/

/-- §4.3 (`esub`): the replaced occurrence's erased contribution equals `e[V] = r`,
    stated at the packet's own gate `g = bit(μ w)`. The G/W-gate answer
    `hGate : g = b` passes to the `esub`'s own insert bit `b = bit(μ s)`; `PB[V,W]`
    (`hPB`) supplies `r = ⋆` when `b` is set. The `keep` branch resolves to
    `bvar κ` and `inst κ r` cancels it (`inst_bvar_hit`). -/
theorem esub_hit_eps_eq {σ : Level → Level} {ρ : List Disp} {j : Nat}
    (hj : j ≤ ρ.length) {r : ETm} {w u : Level}
    (hGate : levelIsZero (σ w) = levelIsZero (σ u))
    (hPB : levelIsZero (σ u) = true → r = .star) :
    (match levelIsZero (σ w) with
     | true => resolve (insertDisp .drop j ρ) j
     | false =>
         ETm.inst (countKeep (ρ.take j)) r
           (resolve (insertDisp .keep j ρ) j)) = r := by
  rw [hGate]
  split <;> rename_i hb
  · exact (resolve_insertDisp_drop j ρ hj).trans (hPB hb).symm
  · rw [resolve_insertDisp_keep j ρ hj]
    exact inst_bvar_hit _ _

/-- §4.3 (R2 `lsub`), `r = ⋆` leg: `drop` is inserted and the occurrence resolves
    to `⋆`; `hPB` is the PB[V,W] answer identifying that value with `e[V]`. -/
theorem lsub_hit_eps_eq_drop {ρ : List Disp} {j : Nat} (hj : j ≤ ρ.length)
    {r : ETm} (hPB : r = .star) :
    resolve (insertDisp .drop j ρ) j = r :=
  (resolve_insertDisp_drop j ρ hj).trans hPB.symm

/-- §4.3 (R2 `lsub`), `r ≠ ⋆` leg: `inline (localize κ r)` is inserted, resolution
    gives `(localize κ r).lift 0 κ`, and the same-stage scope `hScope` cancels the
    lift (`localize_lift_cancel`). `hPB` is the PB[V,W] bit answer `b = false` and
    `hGate` the G/W gate `g = b`; the pair returned is the hit equation plus the
    packet's live-gate fact `g = false`. -/
theorem lsub_hit_eps_eq_inline {σ : Level → Level} {ρ : List Disp} {j : Nat}
    (hj : j ≤ ρ.length) {r : ETm} {w u : Level}
    (hPB : levelIsZero (σ u) = false)
    (hGate : levelIsZero (σ w) = levelIsZero (σ u))
    (hScope : AvoidPrefix (countKeep (ρ.take j)) 0 r) :
    resolve (insertDisp (.inline (localize (countKeep (ρ.take j)) r)) j ρ) j = r ∧
      levelIsZero (σ w) = false :=
  ⟨(resolve_insertDisp_inline j _ ρ hj).trans (localize_lift_cancel hScope),
    hGate.trans hPB⟩

/-- §4.3 (R2 `lsub`), both legs: the erased clause keys the inserted disposition
    on `r`'s own head, so `PB[V,W]` appears as the match itself — `r = ⋆` resolves
    `drop → ⋆`; otherwise `inline (localize κ r)` resolves to
    `(localize κ r).lift 0 κ`, cancelled by same-stage scope. -/
theorem lsub_hit_eps_eq {ρ : List Disp} {j : Nat} (hj : j ≤ ρ.length) {r : ETm}
    (hScope : AvoidPrefix (countKeep (ρ.take j)) 0 r) :
    (match r with
     | .star => resolve (insertDisp .drop j ρ) j
     | ev =>
         resolve (insertDisp (.inline (localize (countKeep (ρ.take j)) ev)) j ρ) j) = r := by
  cases r <;>
    first
      | exact resolve_insertDisp_drop j ρ hj
      | exact (resolve_insertDisp_inline j _ ρ hj).trans (localize_lift_cancel hScope)

end Rcic.Syn

#print axioms Rcic.Syn.instEnd_eps_piSlot_false
#print axioms Rcic.Syn.instEnd_eps_piSlot_true
#print axioms Rcic.Syn.instEnd_eps_piSlot
#print axioms Rcic.Syn.mixedEUT_app_uniform_finish
#print axioms Rcic.Syn.lift_inst_zero
#print axioms Rcic.Syn.inst_inst_zero
#print axioms Rcic.Syn.mixedEUT_one_hit
#print axioms Rcic.Syn.mixedEUT_two_hit
#print axioms Rcic.Syn.esub_hit_eps_eq
#print axioms Rcic.Syn.lsub_hit_eps_eq_drop
#print axioms Rcic.Syn.lsub_hit_eps_eq_inline
#print axioms Rcic.Syn.lsub_hit_eps_eq
