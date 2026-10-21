import rcic.ScmSrcGroupsConv
import rcic.ScmSrcGroupsRecIdx
import rcic.RcicIota

/-! Stage 2c: the full `EnvWf srcEnvG (n+1)` chain, conditional on
`BlockedHidxAdm` — the two `hidxAdm` premises main cannot take yet
(CCT: R-NoFunRec; ValueAt: defect 2). Slot 159 types only at level
bound ≥ 1 (`BL.rec.{1}`), hence `n + 1`.

Supersession note (added post-merge, comment-only): as EVIDENCE this file's
`srcEnvG_wf_of (B : BlockedHidxAdm)` is superseded by the typed
`envWfT_srcEnvG : EnvWfT srcEnvG` (`ScmSrcGroupsEnvWfT.lean`, PR #6225) —
unconditional on the `EnvWfT` lane, slot 159's `srcNthBTyT` discharged by the
hand-built derivation of PR #6205. `BlockedHidxAdm` remains open only on this
legacy root: the untyped ι lane gives function-recursor constructors no field
kinds (R-NoFunRec), so the two `hidxAdm` premises cannot be discharged here;
the typed lane supplies them via `recIdxAdmittedTB` leaves instead. -/

open Rcic.Declarative Rcic.Machine
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/-! ### Level-bound monotonicity (`n` enters only `HasTy.const`) -/

mutual
private def stepLevelMono {E : ResolvedEnv} {n m : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → Step E n Γ a b → Step E m Γ a b
  | _, _, _, .beta _ _ _ _ => .beta _ _ _ _
  | _, _, _, .zeta _ _ _ _ => .zeta _ _ _ _
  | _, _, _, .zetaLocal _ _ _ h => .zetaLocal _ _ _ h
  | _, _, _, .delta _ r ls m' b hres hbody htr =>
      .delta _ r ls m' b hres hbody htr
  | _, _, _, .iota _ _ _ h => .iota _ _ _ h
  | _, _, _, .lit _ _ _ h => .lit _ _ _ h

private def convLevelMono {E : ResolvedEnv} {n m : Nat} (hn : n ≤ m) :
    {Γ : LCtx} → {a b : Expr Nat} → Conv E n Γ a b → Conv E m Γ a b
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .symm _ _ _ h => .symm _ _ _ (convLevelMono hn h)
  | _, _, _, .trans _ _ _ _ h1 h2 => .trans _ _ _ _
      (convLevelMono hn h1) (convLevelMono hn h2)
  | _, _, _, .step _ _ _ hs => .step _ _ _ (stepLevelMono hs)
  | _, _, _, .app _ _ _ _ _ h1 h2 => .app _ _ _ _ _
      (convLevelMono hn h1) (convLevelMono hn h2)
  | _, _, _, .lam _ _ _ _ _ hA hb => .lam _ _ _ _ _
      (convLevelMono hn hA) (convLevelMono hn hb)
  | _, _, _, .pi _ _ _ _ _ hA hb => .pi _ _ _ _ _
      (convLevelMono hn hA) (convLevelMono hn hb)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => .letE _ _ _ _ _ _ _
      (convLevelMono hn hA) (convLevelMono hn hv) (convLevelMono hn hb)
  | _, _, _, .sorts Γ l1 l2 h => .sorts Γ l1 l2 h
  | _, _, _, .consts Γ r ls ls' h => .consts Γ r ls ls' h
  | _, _, _, .eta Γ f A B hh => .eta Γ f A B (hasTyLevelMono hn hh)
  | _, _, _, .irr _ _ _ _ hP hp hq =>
      .irr _ _ _ _ (hasTyLevelMono hn hP) (hasTyLevelMono hn hp)
        (hasTyLevelMono hn hq)

private def hasTyLevelMono {E : ResolvedEnv} {n m : Nat} (hn : n ≤ m) :
    {Γ : LCtx} → {e T : Expr Nat} → HasTy E n Γ e T → HasTy E m Γ e T
  | _, _, _, .sort _ _ => .sort _ _
  | _, _, _, .bvar _ _ _ h => .bvar _ _ _ h
  | _, _, _, .const Γ r ls m' hres hlen hwf =>
      .const Γ r ls m' hres hlen fun l hl =>
        match hwf l hl with
        | ⟨k, h0⟩ => ⟨k, h0.elim Or.inl fun hk =>
            Or.inr (Nat.lt_of_lt_of_le hk hn)⟩
  | _, _, _, .pi _ _ _ _ _ hA hB => .pi _ _ _ _ _
      (hasTyLevelMono hn hA) (hasTyLevelMono hn hB)
  | _, _, _, .lam _ _ _ _ _ hA hb => .lam _ _ _ _ _
      (hasTyLevelMono hn hA) (hasTyLevelMono hn hb)
  | _, _, _, .app _ _ _ _ _ hf ha => .app _ _ _ _ _
      (hasTyLevelMono hn hf) (hasTyLevelMono hn ha)
  | _, _, _, .letE _ _ _ _ _ hA hv hb => .letE _ _ _ _ _
      (hasTyLevelMono hn hA) (hasTyLevelMono hn hv)
      (hasTyLevelMono hn hb)
  | _, _, _, .conv _ _ _ _ h hc => .conv _ _ _ _
      (hasTyLevelMono hn h) (convLevelMono hn hc)
  | _, _, _, .lit _ _ _ hexp => .lit _ _ _ (hasTyLevelMono hn hexp)
end

/-- Local copy of the 2a closedness wrapper. -/
private def lift_id_closed {e : Expr Nat} (h : exprClosedAt 0 e = true) :
    ∀ k, lift k 1 e = e :=
  fun k => lift_eq_of_closedAt_le h (Nat.zero_le k)

private def wfOfExtend {n : Nat} {r : Nat} {m : CheckedMember}
    (hr : r < srcMembersG.length) (hm : srcMembersG[r]'hr = ⟨r, m⟩)
    (h : EnvWf (extendEnv (envPre r) r m) n) : EnvWf (envPre (r+1)) n := by
  rw [envPre_succ hr, hm]
  exact h

private def hasTy_of_inferConvAux {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T : Expr Nat}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (h : (inferConvAux (fun _ => none) (n := n) (Γ := Γ) 65536 h1 h2
      e).map (·.1) = some T) : HasTy E n Γ e T := by
  cases hs : inferConvAux (fun _ => none) (n := n) (Γ := Γ) 65536 h1 h2
      e with
  | none => rw [hs] at h; contradiction
  | some s =>
      rw [hs] at h
      change some s.1 = some T at h
      rw [← Option.some.inj h]
      exact s.2

/-! ## What `EnvWf` still cannot take on main

`EnvWf.indMember` (main, #6084) needs, at every recursor, `IndGroupAdmitted … .recursor` (`hadm`) and `RecursorGroupIdxAdmitted` (`hidxAdm`). Since #6160 (`b2221de20f`) the judgment's ι clause states the motive at the constructor's result indices, and all 26 `hadm` are supplied: the 7 non-indexed in `ScmSrcGroupsRec`, the 19 indexed in `ScmSrcGroupsRecIdx` (from the 05 §14 evidence, through `iotaLhsType_eq_05`, with no conversion step). Of the 26 `hidxAdm`, 24 go through the Bool route. The two fields below are the rest:

* `idxCCT`: the Bool route fails only at `cctSum` 103 and `cctRec` 104. Main's ι gives those two constructors no field kinds (R-NoFunRec, #6151; `noKindCtors_eq`). It is not built by hand: with no ι witness at those two constructors (`noIotaWitness_funRec`), it would hold vacuously exactly there.
* `idxValueAt`: since IDX-R2 the normal admission Bool accepts `vaPair` 140: its compound index `mkBound …` is sourced and typed (`vaPairAdmittedAt`). The field is still not built, because the Bool also runs at `vaList` 139 and `vaR` 142, which main's ι gives no field kinds (R-NoFunRec, #6151; `valueAtFunRecRefused`). Built by hand, it would hold only vacuously there.

Neither field may be filled through `RcicUntypedConvCollapse`. -/
structure BlockedHidxAdm : Type where
  idxCCT : RecursorGroupIdxAdmitted (envPre 105) 105 recCCT
  idxValueAt : RecursorGroupIdxAdmitted (envPre 143) 143 recValueAt

kernel_rfl_theorem rga29 : recursorGroupAdmitted (envPre 29) 29 recDA = true
kernel_rfl_theorem rga33 : recursorGroupAdmitted (envPre 33) 33 recI = true
kernel_rfl_theorem rga37 : recursorGroupAdmitted (envPre 37) 37 recBL = true
kernel_rfl_theorem rga41 : recursorGroupAdmitted (envPre 41) 41 recFT = true
kernel_rfl_theorem rga45 : recursorGroupAdmitted (envPre 45) 45 recLt = true
kernel_rfl_theorem rga49 : recursorGroupAdmitted (envPre 49) 49 recBC = true
kernel_rfl_theorem rga53 : recursorGroupAdmitted (envPre 53) 53 recDM10 = true
kernel_rfl_theorem rga57 : recursorGroupAdmitted (envPre 57) 57 recND = true
kernel_rfl_theorem rga60 : recursorGroupAdmitted (envPre 60) 60 recNEA = true
kernel_rfl_theorem rga64 : recursorGroupAdmitted (envPre 64) 64 recIEA = true
kernel_rfl_theorem rga68 : recursorGroupAdmitted (envPre 68) 68 recSL = true
kernel_rfl_theorem rga72 : recursorGroupAdmitted (envPre 72) 72 recBLL = true
kernel_rfl_theorem rga76 : recursorGroupAdmitted (envPre 76) 76 recFTL = true
kernel_rfl_theorem rga80 : recursorGroupAdmitted (envPre 80) 80 recBLC = true
kernel_rfl_theorem rga83 : recursorGroupAdmitted (envPre 83) 83 recSEA = true
kernel_rfl_theorem rga87 : recursorGroupAdmitted (envPre 87) 87 recFTE = true
kernel_rfl_theorem rga91 : recursorGroupAdmitted (envPre 91) 91 recNthB = true
kernel_rfl_theorem rga95 : recursorGroupAdmitted (envPre 95) 95 recNthF = true
kernel_rfl_theorem rga108 : recursorGroupAdmitted (envPre 108) 108 recBCT = true
kernel_rfl_theorem rga128 : recursorGroupAdmitted (envPre 128) 128 recNEL = true
kernel_rfl_theorem rga132 : recursorGroupAdmitted (envPre 132) 132 recNTB = true
private def infTy109 (n : Nat)
    (h1 : (envPre 109).members 1 = some mZero)
    (h2 : (envPre 109).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 109) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mI64Ref.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy109 (n : Nat)
    (h1 : (envPre 109).members 1 = some mZero)
    (h2 : (envPre 109).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 109) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mI64Ref.body.getD (.sort .zero))).map (·.1) = some (mI64Ref.mtype) := rfl
private def infTy110 (n : Nat)
    (h1 : (envPre 110).members 1 = some mZero)
    (h2 : (envPre 110).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 110) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoolRef.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy110 (n : Nat)
    (h1 : (envPre 110).members 1 = some mZero)
    (h2 : (envPre 110).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 110) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoolRef.body.getD (.sort .zero))).map (·.1) = some (mBoolRef.mtype) := rfl
private def infTy111 (n : Nat)
    (h1 : (envPre 111).members 1 = some mZero)
    (h2 : (envPre 111).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 111) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mStrRef.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy111 (n : Nat)
    (h1 : (envPre 111).members 1 = some mZero)
    (h2 : (envPre 111).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 111) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mStrRef.body.getD (.sort .zero))).map (·.1) = some (mStrRef.mtype) := rfl
private def infTy112 (n : Nat)
    (h1 : (envPre 112).members 1 = some mZero)
    (h2 : (envPre 112).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 112) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesRef.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy112 (n : Nat)
    (h1 : (envPre 112).members 1 = some mZero)
    (h2 : (envPre 112).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 112) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesRef.body.getD (.sort .zero))).map (·.1) = some (mBytesRef.mtype) := rfl
private def infTy117 (n : Nat)
    (h1 : (envPre 117).members 1 = some mZero)
    (h2 : (envPre 117).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 117) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundI64.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy117 (n : Nat)
    (h1 : (envPre 117).members 1 = some mZero)
    (h2 : (envPre 117).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 117) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundI64.body.getD (.sort .zero))).map (·.1) = some (mBoundI64.mtype) := rfl
private def infTy118 (n : Nat)
    (h1 : (envPre 118).members 1 = some mZero)
    (h2 : (envPre 118).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 118) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundBool.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy118 (n : Nat)
    (h1 : (envPre 118).members 1 = some mZero)
    (h2 : (envPre 118).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 118) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundBool.body.getD (.sort .zero))).map (·.1) = some (mBoundBool.mtype) := rfl
private def infTy119 (n : Nat)
    (h1 : (envPre 119).members 1 = some mZero)
    (h2 : (envPre 119).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 119) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundStr.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy119 (n : Nat)
    (h1 : (envPre 119).members 1 = some mZero)
    (h2 : (envPre 119).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 119) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundStr.body.getD (.sort .zero))).map (·.1) = some (mBoundStr.mtype) := rfl
private def infTy120 (n : Nat)
    (h1 : (envPre 120).members 1 = some mZero)
    (h2 : (envPre 120).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 120) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundBytes.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy120 (n : Nat)
    (h1 : (envPre 120).members 1 = some mZero)
    (h2 : (envPre 120).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 120) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundBytes.body.getD (.sort .zero))).map (·.1) = some (mBoundBytes.mtype) := rfl
private def infTy122 (n : Nat)
    (h1 : (envPre 122).members 1 = some mZero)
    (h2 : (envPre 122).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 122) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mLbRef.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy122 (n : Nat)
    (h1 : (envPre 122).members 1 = some mZero)
    (h2 : (envPre 122).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 122) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mLbRef.body.getD (.sort .zero))).map (·.1) = some (mLbRef.mtype) := rfl
private def infTy124 (n : Nat)
    (h1 : (envPre 124).members 1 = some mZero)
    (h2 : (envPre 124).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 124) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundListBool.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy124 (n : Nat)
    (h1 : (envPre 124).members 1 = some mZero)
    (h2 : (envPre 124).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 124) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBoundListBool.body.getD (.sort .zero))).map (·.1) = some (mBoundListBool.mtype) := rfl
private def infTy146 (n : Nat)
    (h1 : (envPre 146).members 1 = some mZero)
    (h2 : (envPre 146).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 146) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesSemi.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy146 (n : Nat)
    (h1 : (envPre 146).members 1 = some mZero)
    (h2 : (envPre 146).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 146) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesSemi.body.getD (.sort .zero))).map (·.1) = some (mBytesSemi.mtype) := rfl
private def infTy147 (n : Nat)
    (h1 : (envPre 147).members 1 = some mZero)
    (h2 : (envPre 147).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 147) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesD0.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy147 (n : Nat)
    (h1 : (envPre 147).members 1 = some mZero)
    (h2 : (envPre 147).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 147) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesD0.body.getD (.sort .zero))).map (·.1) = some (mBytesD0.mtype) := rfl
private def infTy148 (n : Nat)
    (h1 : (envPre 148).members 1 = some mZero)
    (h2 : (envPre 148).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 148) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesNat0.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy148 (n : Nat)
    (h1 : (envPre 148).members 1 = some mZero)
    (h2 : (envPre 148).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 148) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesNat0.body.getD (.sort .zero))).map (·.1) = some (mBytesNat0.mtype) := rfl
private def infTy149 (n : Nat)
    (h1 : (envPre 149).members 1 = some mZero)
    (h2 : (envPre 149).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 149) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesVLB0.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy149 (n : Nat)
    (h1 : (envPre 149).members 1 = some mZero)
    (h2 : (envPre 149).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 149) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesVLB0.body.getD (.sort .zero))).map (·.1) = some (mBytesVLB0.mtype) := rfl
private def infTy150 (n : Nat)
    (h1 : (envPre 150).members 1 = some mZero)
    (h2 : (envPre 150).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 150) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesI5.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy150 (n : Nat)
    (h1 : (envPre 150).members 1 = some mZero)
    (h2 : (envPre 150).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 150) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesI5.body.getD (.sort .zero))).map (·.1) = some (mBytesI5.mtype) := rfl
private def infTy151 (n : Nat)
    (h1 : (envPre 151).members 1 = some mZero)
    (h2 : (envPre 151).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 151) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesD5.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy151 (n : Nat)
    (h1 : (envPre 151).members 1 = some mZero)
    (h2 : (envPre 151).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 151) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesD5.body.getD (.sort .zero))).map (·.1) = some (mBytesD5.mtype) := rfl
private def infTy152 (n : Nat)
    (h1 : (envPre 152).members 1 = some mZero)
    (h2 : (envPre 152).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 152) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesNat5.mtype)).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy152 (n : Nat)
    (h1 : (envPre 152).members 1 = some mZero)
    (h2 : (envPre 152).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 152) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mBytesNat5.body.getD (.sort .zero))).map (·.1) = some (mBytesNat5.mtype) := rfl
kernel_rfl_theorem infA113 : (inferConvAux (fun _ => none)
    (E := envPre 113) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctI64Pf.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA114 : (inferConvAux (fun _ => none)
    (E := envPre 114) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctBoolPf.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA115 : (inferConvAux (fun _ => none)
    (E := envPre 115) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctStrPf.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA116 : (inferConvAux (fun _ => none)
    (E := envPre 116) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctBytesPf.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA121 : (inferConvAux (fun _ => none)
    (E := envPre 121) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcLB.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA123 : (inferConvAux (fun _ => none)
    (E := envPre 123) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctLbPf.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA144 : (inferConvAux (fun _ => none)
    (E := envPre 144) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVb0.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA145 : (inferConvAux (fun _ => none)
    (E := envPre 145) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVb1.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA153 : (inferConvAux (fun _ => none)
    (E := envPre 153) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mLt010.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA154 : (inferConvAux (fun _ => none)
    (E := envPre 154) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNd0.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA155 : (inferConvAux (fun _ => none)
    (E := envPre 155) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBc48S.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA156 : (inferConvAux (fun _ => none)
    (E := envPre 156) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNea0.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA157 : (inferConvAux (fun _ => none)
    (E := envPre 157) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcLN0.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA158 : (inferConvAux (fun _ => none)
    (E := envPre 158) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcL0Nil.mtype)).map (·.1) = some (.sort .zero)
/- Slot 159's type infers at `Sort (imax 1 (imax 1 (imax 0 0)))`,
which is `Sort 0` only up to `eqN`; `tyType159` converts by
`Conv.sorts`. -/
kernel_rfl_theorem infA159 : (inferConvAux (fun _ => none)
    (E := envPre 159) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNthBNilVa.mtype)).map (·.1) =
      some (.sort (.imax (.succ .zero) (.imax (.succ .zero)
        (.imax .zero .zero))))
kernel_rfl_theorem infA160 : (inferConvAux (fun _ => none)
    (E := envPre 160) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVLBNil.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA161 : (inferConvAux (fun _ => none)
    (E := envPre 161) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mLt510.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA162 : (inferConvAux (fun _ => none)
    (E := envPre 162) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNd5.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA163 : (inferConvAux (fun _ => none)
    (E := envPre 163) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBc53S.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA164 : (inferConvAux (fun _ => none)
    (E := envPre 164) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNea5.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA165 : (inferConvAux (fun _ => none)
    (E := envPre 165) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mIeaP5.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA166 : (inferConvAux (fun _ => none)
    (E := envPre 166) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcI5.mtype)).map (·.1) = some (.sort .zero)
kernel_rfl_theorem infA167 : (inferConvAux (fun _ => none)
    (E := envPre 167) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVI5.mtype)).map (·.1) = some (.sort .zero)
private def infBdy156 (n : Nat)
    (h1 : (envPre 156).members 1 = some mZero)
    (h2 : (envPre 156).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 156) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mNea0.body.getD (.sort .zero))).map (·.1) = some (mNea0.mtype) := rfl
private def infBdy164 (n : Nat)
    (h1 : (envPre 164).members 1 = some mZero)
    (h2 : (envPre 164).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 164) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mNea5.body.getD (.sort .zero))).map (·.1) = some (mNea5.mtype) := rfl
private def infBdy165 (n : Nat)
    (h1 : (envPre 165).members 1 = some mZero)
    (h2 : (envPre 165).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 165) (n := n+1) (Γ := ([] : LCtx)) h1 h2
      (mIeaP5.body.getD (.sort .zero))).map (·.1) = some (mIeaP5.mtype) := rfl
/- Slot 166's body infers at the δ-unfolded `c150`, so it is checked
by conversion rather than read off `inferSpine2`. -/
kernel_rfl_theorem chkThm166 :
    (checkConv (E := envPre 166) (n := 0) (Γ := ([] : LCtx)) 65536
      (by rfl) (by rfl)
      (mBcI5.body.getD (.sort .zero)) mBcI5.mtype).isSome = true
private def tyBody166 : HasTy (envPre 166) 0 []
    (mBcI5.body.getD (.sort .zero)) mBcI5.mtype :=
  Option.get (checkConv (E := envPre 166) (n := 0) (Γ := ([] : LCtx))
    65536 rfl rfl (mBcI5.body.getD (.sort .zero)) mBcI5.mtype) chkThm166
private def tyType159 : HasTy (envPre 159) 0 [] mNthBNilVa.mtype
    (.sort .zero) :=
  .conv _ _ _ _ (hasTy_of_inferConvAux rfl rfl infA159)
    (.sorts _ _ _ (fun _ => rfl))
private def tyBody113 : HasTy (envPre 113) 0 []
    (mCctI64Pf.body.getD (.sort .zero)) mCctI64Pf.mtype :=
  Option.get (checkConv (E := envPre 113) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctI64Pf.body.getD (.sort .zero)) mCctI64Pf.mtype) chkThm113
private def tyBody114 : HasTy (envPre 114) 0 []
    (mCctBoolPf.body.getD (.sort .zero)) mCctBoolPf.mtype :=
  Option.get (checkConv (E := envPre 114) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctBoolPf.body.getD (.sort .zero)) mCctBoolPf.mtype) chkThm114
private def tyBody115 : HasTy (envPre 115) 0 []
    (mCctStrPf.body.getD (.sort .zero)) mCctStrPf.mtype :=
  Option.get (checkConv (E := envPre 115) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctStrPf.body.getD (.sort .zero)) mCctStrPf.mtype) chkThm115
private def tyBody116 : HasTy (envPre 116) 0 []
    (mCctBytesPf.body.getD (.sort .zero)) mCctBytesPf.mtype :=
  Option.get (checkConv (E := envPre 116) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctBytesPf.body.getD (.sort .zero)) mCctBytesPf.mtype) chkThm116
private def tyBody121 : HasTy (envPre 121) 0 []
    (mBcLB.body.getD (.sort .zero)) mBcLB.mtype :=
  Option.get (checkConv (E := envPre 121) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcLB.body.getD (.sort .zero)) mBcLB.mtype) chkThm121
private def tyBody123 : HasTy (envPre 123) 0 []
    (mCctLbPf.body.getD (.sort .zero)) mCctLbPf.mtype :=
  Option.get (checkConv (E := envPre 123) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mCctLbPf.body.getD (.sort .zero)) mCctLbPf.mtype) chkThm123
private def tyBody144 : HasTy (envPre 144) 0 []
    (mVb0.body.getD (.sort .zero)) mVb0.mtype :=
  Option.get (checkConv (E := envPre 144) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVb0.body.getD (.sort .zero)) mVb0.mtype) chkThm144
private def tyBody145 : HasTy (envPre 145) 0 []
    (mVb1.body.getD (.sort .zero)) mVb1.mtype :=
  Option.get (checkConv (E := envPre 145) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVb1.body.getD (.sort .zero)) mVb1.mtype) chkThm145
private def tyBody153 : HasTy (envPre 153) 0 []
    (mLt010.body.getD (.sort .zero)) mLt010.mtype :=
  Option.get (checkConv (E := envPre 153) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mLt010.body.getD (.sort .zero)) mLt010.mtype) chkThm153
private def tyBody154 : HasTy (envPre 154) 0 []
    (mNd0.body.getD (.sort .zero)) mNd0.mtype :=
  Option.get (checkConv (E := envPre 154) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNd0.body.getD (.sort .zero)) mNd0.mtype) chkThm154
private def tyBody155 : HasTy (envPre 155) 0 []
    (mBc48S.body.getD (.sort .zero)) mBc48S.mtype :=
  Option.get (checkConv (E := envPre 155) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBc48S.body.getD (.sort .zero)) mBc48S.mtype) chkThm155
private def tyBody157 : HasTy (envPre 157) 0 []
    (mBcLN0.body.getD (.sort .zero)) mBcLN0.mtype :=
  Option.get (checkConv (E := envPre 157) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcLN0.body.getD (.sort .zero)) mBcLN0.mtype) chkThm157
private def tyBody158 : HasTy (envPre 158) 0 []
    (mBcL0Nil.body.getD (.sort .zero)) mBcL0Nil.mtype :=
  Option.get (checkConv (E := envPre 158) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBcL0Nil.body.getD (.sort .zero)) mBcL0Nil.mtype) chkThm158
private def tyBody161 : HasTy (envPre 161) 0 []
    (mLt510.body.getD (.sort .zero)) mLt510.mtype :=
  Option.get (checkConv (E := envPre 161) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mLt510.body.getD (.sort .zero)) mLt510.mtype) chkThm161
private def tyBody162 : HasTy (envPre 162) 0 []
    (mNd5.body.getD (.sort .zero)) mNd5.mtype :=
  Option.get (checkConv (E := envPre 162) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mNd5.body.getD (.sort .zero)) mNd5.mtype) chkThm162
private def tyBody163 : HasTy (envPre 163) 0 []
    (mBc53S.body.getD (.sort .zero)) mBc53S.mtype :=
  Option.get (checkConv (E := envPre 163) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mBc53S.body.getD (.sort .zero)) mBc53S.mtype) chkThm163
private def tyBody167 : HasTy (envPre 167) 0 []
    (mVI5.body.getD (.sort .zero)) mVI5.mtype :=
  Option.get (checkConv (E := envPre 167) (n := 0) (Γ := ([] : LCtx)) 65536 rfl rfl
    (mVI5.body.getD (.sort .zero)) mVI5.mtype) chkThm167

set_option maxHeartbeats 0 in
noncomputable def srcEnvG_wf_of (B : BlockedHidxAdm) (n : Nat) : EnvWf srcEnvG (n+1) := by
  have w29 : EnvWf (envPre 29) (n+1) := srcEnvG_prefix_wf (n+1)
  have w30 : EnvWf (envPre 30) (n+1) :=
    wfOfExtend (r := 29) (m := recDA) (by decide) rfl
      (.indMember (envPre 29) 29 recDA w29 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga29) admRecDA)
  have w31 : EnvWf (envPre 31) (n+1) :=
    wfOfExtend (r := 30) (m := mI) (by decide) rfl
      (.indMember (envPre 30) 30 mI w30 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamI)
  have w32 : EnvWf (envPre 32) (n+1) :=
    wfOfExtend (r := 31) (m := mIPos) (by decide) rfl
      (.indMember (envPre 31) 31 mIPos w31 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorIPos)
  have w33 : EnvWf (envPre 33) (n+1) :=
    wfOfExtend (r := 32) (m := mINegS) (by decide) rfl
      (.indMember (envPre 32) 32 mINegS w32 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorINegS)
  have w34 : EnvWf (envPre 34) (n+1) :=
    wfOfExtend (r := 33) (m := recI) (by decide) rfl
      (.indMember (envPre 33) 33 recI w33 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga33) admRecI)
  have w35 : EnvWf (envPre 35) (n+1) :=
    wfOfExtend (r := 34) (m := mBL) (by decide) rfl
      (.indMember (envPre 34) 34 mBL w34 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamBL)
  have w36 : EnvWf (envPre 36) (n+1) :=
    wfOfExtend (r := 35) (m := mBlNil) (by decide) rfl
      (.indMember (envPre 35) 35 mBlNil w35 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBlNil)
  have w37 : EnvWf (envPre 37) (n+1) :=
    wfOfExtend (r := 36) (m := mBlCons) (by decide) rfl
      (.indMember (envPre 36) 36 mBlCons w36 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBlCons)
  have w38 : EnvWf (envPre 38) (n+1) :=
    wfOfExtend (r := 37) (m := recBL) (by decide) rfl
      (.indMember (envPre 37) 37 recBL w37 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga37) admRecBL)
  have w39 : EnvWf (envPre 39) (n+1) :=
    wfOfExtend (r := 38) (m := mFT) (by decide) rfl
      (.indMember (envPre 38) 38 mFT w38 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamFT)
  have w40 : EnvWf (envPre 40) (n+1) :=
    wfOfExtend (r := 39) (m := mFtNil) (by decide) rfl
      (.indMember (envPre 39) 39 mFtNil w39 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorFtNil)
  have w41 : EnvWf (envPre 41) (n+1) :=
    wfOfExtend (r := 40) (m := mFtCons) (by decide) rfl
      (.indMember (envPre 40) 40 mFtCons w40 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorFtCons)
  have w42 : EnvWf (envPre 42) (n+1) :=
    wfOfExtend (r := 41) (m := recFT) (by decide) rfl
      (.indMember (envPre 41) 41 recFT w41 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga41) admRecFT)
  have w43 : EnvWf (envPre 43) (n+1) :=
    wfOfExtend (r := 42) (m := mLt) (by decide) rfl
      (.indMember (envPre 42) 42 mLt w42 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamLt)
  have w44 : EnvWf (envPre 44) (n+1) :=
    wfOfExtend (r := 43) (m := mLtBase) (by decide) rfl
      (.indMember (envPre 43) 43 mLtBase w43 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorLtBase)
  have w45 : EnvWf (envPre 45) (n+1) :=
    wfOfExtend (r := 44) (m := mLtStep) (by decide) rfl
      (.indMember (envPre 44) 44 mLtStep w44 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorLtStep)
  have w46 : EnvWf (envPre 46) (n+1) :=
    wfOfExtend (r := 45) (m := recLt) (by decide) rfl
      (.indMember (envPre 45) 45 recLt w45 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga45) admRecLt)
  have w47 : EnvWf (envPre 47) (n+1) :=
    wfOfExtend (r := 46) (m := mBC) (by decide) rfl
      (.indMember (envPre 46) 46 mBC w46 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamBC)
  have w48 : EnvWf (envPre 48) (n+1) :=
    wfOfExtend (r := 47) (m := mCatNil) (by decide) rfl
      (.indMember (envPre 47) 47 mCatNil w47 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCatNil)
  have w49 : EnvWf (envPre 49) (n+1) :=
    wfOfExtend (r := 48) (m := mCatCons) (by decide) rfl
      (.indMember (envPre 48) 48 mCatCons w48 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCatCons)
  have w50 : EnvWf (envPre 50) (n+1) :=
    wfOfExtend (r := 49) (m := recBC) (by decide) rfl
      (.indMember (envPre 49) 49 recBC w49 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga49) admRecBC)
  have w51 : EnvWf (envPre 51) (n+1) :=
    wfOfExtend (r := 50) (m := mDM10) (by decide) rfl
      (.indMember (envPre 50) 50 mDM10 w50 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamDM10)
  have w52 : EnvWf (envPre 52) (n+1) :=
    wfOfExtend (r := 51) (m := mDmBase) (by decide) rfl
      (.indMember (envPre 51) 51 mDmBase w51 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDmBase)
  have w53 : EnvWf (envPre 53) (n+1) :=
    wfOfExtend (r := 52) (m := mDmStep) (by decide) rfl
      (.indMember (envPre 52) 52 mDmStep w52 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDmStep)
  have w54 : EnvWf (envPre 54) (n+1) :=
    wfOfExtend (r := 53) (m := recDM10) (by decide) rfl
      (.indMember (envPre 53) 53 recDM10 w53 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga53) admRecDM10)
  have w55 : EnvWf (envPre 55) (n+1) :=
    wfOfExtend (r := 54) (m := mND) (by decide) rfl
      (.indMember (envPre 54) 54 mND w54 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamND)
  have w56 : EnvWf (envPre 56) (n+1) :=
    wfOfExtend (r := 55) (m := mNdBase) (by decide) rfl
      (.indMember (envPre 55) 55 mNdBase w55 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNdBase)
  have w57 : EnvWf (envPre 57) (n+1) :=
    wfOfExtend (r := 56) (m := mNdStep) (by decide) rfl
      (.indMember (envPre 56) 56 mNdStep w56 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNdStep)
  have w58 : EnvWf (envPre 58) (n+1) :=
    wfOfExtend (r := 57) (m := recND) (by decide) rfl
      (.indMember (envPre 57) 57 recND w57 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga57) admRecND)
  have w59 : EnvWf (envPre 59) (n+1) :=
    wfOfExtend (r := 58) (m := mNEA) (by decide) rfl
      (.indMember (envPre 58) 58 mNEA w58 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamNEA)
  have w60 : EnvWf (envPre 60) (n+1) :=
    wfOfExtend (r := 59) (m := mNeIntro) (by decide) rfl
      (.indMember (envPre 59) 59 mNeIntro w59 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNeIntro)
  have w61 : EnvWf (envPre 61) (n+1) :=
    wfOfExtend (r := 60) (m := recNEA) (by decide) rfl
      (.indMember (envPre 60) 60 recNEA w60 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga60) admRecNEA)
  have w62 : EnvWf (envPre 62) (n+1) :=
    wfOfExtend (r := 61) (m := mIEA) (by decide) rfl
      (.indMember (envPre 61) 61 mIEA w61 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamIEA)
  have w63 : EnvWf (envPre 63) (n+1) :=
    wfOfExtend (r := 62) (m := mIePos) (by decide) rfl
      (.indMember (envPre 62) 62 mIePos w62 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorIePos)
  have w64 : EnvWf (envPre 64) (n+1) :=
    wfOfExtend (r := 63) (m := mIeNeg) (by decide) rfl
      (.indMember (envPre 63) 63 mIeNeg w63 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorIeNeg)
  have w65 : EnvWf (envPre 65) (n+1) :=
    wfOfExtend (r := 64) (m := recIEA) (by decide) rfl
      (.indMember (envPre 64) 64 recIEA w64 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga64) admRecIEA)
  have w66 : EnvWf (envPre 66) (n+1) :=
    wfOfExtend (r := 65) (m := mSL) (by decide) rfl
      (.indMember (envPre 65) 65 mSL w65 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamSL)
  have w67 : EnvWf (envPre 67) (n+1) :=
    wfOfExtend (r := 66) (m := mSlNil) (by decide) rfl
      (.indMember (envPre 66) 66 mSlNil w66 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorSlNil)
  have w68 : EnvWf (envPre 68) (n+1) :=
    wfOfExtend (r := 67) (m := mSlCons) (by decide) rfl
      (.indMember (envPre 67) 67 mSlCons w67 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorSlCons)
  have w69 : EnvWf (envPre 69) (n+1) :=
    wfOfExtend (r := 68) (m := recSL) (by decide) rfl
      (.indMember (envPre 68) 68 recSL w68 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga68) admRecSL)
  have w70 : EnvWf (envPre 70) (n+1) :=
    wfOfExtend (r := 69) (m := mBLL) (by decide) rfl
      (.indMember (envPre 69) 69 mBLL w69 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamBLL)
  have w71 : EnvWf (envPre 71) (n+1) :=
    wfOfExtend (r := 70) (m := mBllNil) (by decide) rfl
      (.indMember (envPre 70) 70 mBllNil w70 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBllNil)
  have w72 : EnvWf (envPre 72) (n+1) :=
    wfOfExtend (r := 71) (m := mBllCons) (by decide) rfl
      (.indMember (envPre 71) 71 mBllCons w71 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBllCons)
  have w73 : EnvWf (envPre 73) (n+1) :=
    wfOfExtend (r := 72) (m := recBLL) (by decide) rfl
      (.indMember (envPre 72) 72 recBLL w72 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga72) admRecBLL)
  have w74 : EnvWf (envPre 74) (n+1) :=
    wfOfExtend (r := 73) (m := mFTL) (by decide) rfl
      (.indMember (envPre 73) 73 mFTL w73 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamFTL)
  have w75 : EnvWf (envPre 75) (n+1) :=
    wfOfExtend (r := 74) (m := mFtlNil) (by decide) rfl
      (.indMember (envPre 74) 74 mFtlNil w74 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorFtlNil)
  have w76 : EnvWf (envPre 76) (n+1) :=
    wfOfExtend (r := 75) (m := mFtlCons) (by decide) rfl
      (.indMember (envPre 75) 75 mFtlCons w75 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorFtlCons)
  have w77 : EnvWf (envPre 77) (n+1) :=
    wfOfExtend (r := 76) (m := recFTL) (by decide) rfl
      (.indMember (envPre 76) 76 recFTL w76 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga76) admRecFTL)
  have w78 : EnvWf (envPre 78) (n+1) :=
    wfOfExtend (r := 77) (m := mBLC) (by decide) rfl
      (.indMember (envPre 77) 77 mBLC w77 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamBLC)
  have w79 : EnvWf (envPre 79) (n+1) :=
    wfOfExtend (r := 78) (m := mBlcNil) (by decide) rfl
      (.indMember (envPre 78) 78 mBlcNil w78 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBlcNil)
  have w80 : EnvWf (envPre 80) (n+1) :=
    wfOfExtend (r := 79) (m := mBlcCons) (by decide) rfl
      (.indMember (envPre 79) 79 mBlcCons w79 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBlcCons)
  have w81 : EnvWf (envPre 81) (n+1) :=
    wfOfExtend (r := 80) (m := recBLC) (by decide) rfl
      (.indMember (envPre 80) 80 recBLC w80 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga80) admRecBLC)
  have w82 : EnvWf (envPre 82) (n+1) :=
    wfOfExtend (r := 81) (m := mSEA) (by decide) rfl
      (.indMember (envPre 81) 81 mSEA w81 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamSEA)
  have w83 : EnvWf (envPre 83) (n+1) :=
    wfOfExtend (r := 82) (m := mSeIntro) (by decide) rfl
      (.indMember (envPre 82) 82 mSeIntro w82 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorSeIntro)
  have w84 : EnvWf (envPre 84) (n+1) :=
    wfOfExtend (r := 83) (m := recSEA) (by decide) rfl
      (.indMember (envPre 83) 83 recSEA w83 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga83) admRecSEA)
  have w85 : EnvWf (envPre 85) (n+1) :=
    wfOfExtend (r := 84) (m := mFTE) (by decide) rfl
      (.indMember (envPre 84) 84 mFTE w84 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamFTE)
  have w86 : EnvWf (envPre 86) (n+1) :=
    wfOfExtend (r := 85) (m := mFteNil) (by decide) rfl
      (.indMember (envPre 85) 85 mFteNil w85 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorFteNil)
  have w87 : EnvWf (envPre 87) (n+1) :=
    wfOfExtend (r := 86) (m := mFteCons) (by decide) rfl
      (.indMember (envPre 86) 86 mFteCons w86 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorFteCons)
  have w88 : EnvWf (envPre 88) (n+1) :=
    wfOfExtend (r := 87) (m := recFTE) (by decide) rfl
      (.indMember (envPre 87) 87 recFTE w87 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga87) admRecFTE)
  have w89 : EnvWf (envPre 89) (n+1) :=
    wfOfExtend (r := 88) (m := mNthB) (by decide) rfl
      (.indMember (envPre 88) 88 mNthB w88 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamNthB)
  have w90 : EnvWf (envPre 90) (n+1) :=
    wfOfExtend (r := 89) (m := mNthBHere) (by decide) rfl
      (.indMember (envPre 89) 89 mNthBHere w89 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNthBHere)
  have w91 : EnvWf (envPre 91) (n+1) :=
    wfOfExtend (r := 90) (m := mNthBNext) (by decide) rfl
      (.indMember (envPre 90) 90 mNthBNext w90 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNthBNext)
  have w92 : EnvWf (envPre 92) (n+1) :=
    wfOfExtend (r := 91) (m := recNthB) (by decide) rfl
      (.indMember (envPre 91) 91 recNthB w91 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga91) admRecNthB)
  have w93 : EnvWf (envPre 93) (n+1) :=
    wfOfExtend (r := 92) (m := mNthF) (by decide) rfl
      (.indMember (envPre 92) 92 mNthF w92 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamNthF)
  have w94 : EnvWf (envPre 94) (n+1) :=
    wfOfExtend (r := 93) (m := mNthFHere) (by decide) rfl
      (.indMember (envPre 93) 93 mNthFHere w93 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNthFHere)
  have w95 : EnvWf (envPre 95) (n+1) :=
    wfOfExtend (r := 94) (m := mNthFNext) (by decide) rfl
      (.indMember (envPre 94) 94 mNthFNext w94 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNthFNext)
  have w96 : EnvWf (envPre 96) (n+1) :=
    wfOfExtend (r := 95) (m := recNthF) (by decide) rfl
      (.indMember (envPre 95) 95 recNthF w95 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga95) admRecNthF)
  have w97 : EnvWf (envPre 97) (n+1) :=
    wfOfExtend (r := 96) (m := mCCT) (by decide) rfl
      (.indMember (envPre 96) 96 mCCT w96 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamCCT)
  have w98 : EnvWf (envPre 98) (n+1) :=
    wfOfExtend (r := 97) (m := mCctI) (by decide) rfl
      (.indMember (envPre 97) 97 mCctI w97 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctI)
  have w99 : EnvWf (envPre 99) (n+1) :=
    wfOfExtend (r := 98) (m := mCctB) (by decide) rfl
      (.indMember (envPre 98) 98 mCctB w98 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctB)
  have w100 : EnvWf (envPre 100) (n+1) :=
    wfOfExtend (r := 99) (m := mCctStr) (by decide) rfl
      (.indMember (envPre 99) 99 mCctStr w99 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctStr)
  have w101 : EnvWf (envPre 101) (n+1) :=
    wfOfExtend (r := 100) (m := mCctY) (by decide) rfl
      (.indMember (envPre 100) 100 mCctY w100 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctY)
  have w102 : EnvWf (envPre 102) (n+1) :=
    wfOfExtend (r := 101) (m := mCctL) (by decide) rfl
      (.indMember (envPre 101) 101 mCctL w101 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctL)
  have w103 : EnvWf (envPre 103) (n+1) :=
    wfOfExtend (r := 102) (m := mCctP) (by decide) rfl
      (.indMember (envPre 102) 102 mCctP w102 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctP)
  have w104 : EnvWf (envPre 104) (n+1) :=
    wfOfExtend (r := 103) (m := mCctSum) (by decide) rfl
      (.indMember (envPre 103) 103 mCctSum w103 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctSum)
  have w105 : EnvWf (envPre 105) (n+1) :=
    wfOfExtend (r := 104) (m := mCctRec) (by decide) rfl
      (.indMember (envPre 104) 104 mCctRec w104 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorCctRec)
  have w106 : EnvWf (envPre 106) (n+1) :=
    wfOfExtend (r := 105) (m := recCCT) (by decide) rfl
      (.indMember (envPre 105) 105 recCCT w105 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => B.idxCCT) admRecCCT)
  have w107 : EnvWf (envPre 107) (n+1) :=
    wfOfExtend (r := 106) (m := mBCT) (by decide) rfl
      (.indMember (envPre 106) 106 mBCT w106 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamBCT)
  have w108 : EnvWf (envPre 108) (n+1) :=
    wfOfExtend (r := 107) (m := mMkBound) (by decide) rfl
      (.indMember (envPre 107) 107 mMkBound w107 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorMkBound)
  have w109 : EnvWf (envPre 109) (n+1) :=
    wfOfExtend (r := 108) (m := recBCT) (by decide) rfl
      (.indMember (envPre 108) 108 recBCT w108 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga108) admRecBCT)
  have w110 : EnvWf (envPre 110) (n+1) :=
    wfOfExtend (r := 109) (m := mI64Ref) (by decide) rfl
      (.definition (envPre 109) 109 mI64Ref.mtype
        (mI64Ref.body.getD (.sort .zero)) (.succ .zero) w109 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy109 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy109 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w111 : EnvWf (envPre 111) (n+1) :=
    wfOfExtend (r := 110) (m := mBoolRef) (by decide) rfl
      (.definition (envPre 110) 110 mBoolRef.mtype
        (mBoolRef.body.getD (.sort .zero)) (.succ .zero) w110 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy110 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy110 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w112 : EnvWf (envPre 112) (n+1) :=
    wfOfExtend (r := 111) (m := mStrRef) (by decide) rfl
      (.definition (envPre 111) 111 mStrRef.mtype
        (mStrRef.body.getD (.sort .zero)) (.succ .zero) w111 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy111 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy111 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w113 : EnvWf (envPre 113) (n+1) :=
    wfOfExtend (r := 112) (m := mBytesRef) (by decide) rfl
      (.definition (envPre 112) 112 mBytesRef.mtype
        (mBytesRef.body.getD (.sort .zero)) (.succ .zero) w112 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy112 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy112 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w114 : EnvWf (envPre 114) (n+1) :=
    wfOfExtend (r := 113) (m := mCctI64Pf) (by decide) rfl
      (.thm (envPre 113) 113 mCctI64Pf.mtype
        (mCctI64Pf.body.getD (.sort .zero)) w113 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA113))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody113)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w115 : EnvWf (envPre 115) (n+1) :=
    wfOfExtend (r := 114) (m := mCctBoolPf) (by decide) rfl
      (.thm (envPre 114) 114 mCctBoolPf.mtype
        (mCctBoolPf.body.getD (.sort .zero)) w114 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA114))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody114)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w116 : EnvWf (envPre 116) (n+1) :=
    wfOfExtend (r := 115) (m := mCctStrPf) (by decide) rfl
      (.thm (envPre 115) 115 mCctStrPf.mtype
        (mCctStrPf.body.getD (.sort .zero)) w115 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA115))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody115)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w117 : EnvWf (envPre 117) (n+1) :=
    wfOfExtend (r := 116) (m := mCctBytesPf) (by decide) rfl
      (.thm (envPre 116) 116 mCctBytesPf.mtype
        (mCctBytesPf.body.getD (.sort .zero)) w116 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA116))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody116)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w118 : EnvWf (envPre 118) (n+1) :=
    wfOfExtend (r := 117) (m := mBoundI64) (by decide) rfl
      (.definition (envPre 117) 117 mBoundI64.mtype
        (mBoundI64.body.getD (.sort .zero)) (.succ .zero) w117 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy117 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy117 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w119 : EnvWf (envPre 119) (n+1) :=
    wfOfExtend (r := 118) (m := mBoundBool) (by decide) rfl
      (.definition (envPre 118) 118 mBoundBool.mtype
        (mBoundBool.body.getD (.sort .zero)) (.succ .zero) w118 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy118 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy118 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w120 : EnvWf (envPre 120) (n+1) :=
    wfOfExtend (r := 119) (m := mBoundStr) (by decide) rfl
      (.definition (envPre 119) 119 mBoundStr.mtype
        (mBoundStr.body.getD (.sort .zero)) (.succ .zero) w119 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy119 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy119 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w121 : EnvWf (envPre 121) (n+1) :=
    wfOfExtend (r := 120) (m := mBoundBytes) (by decide) rfl
      (.definition (envPre 120) 120 mBoundBytes.mtype
        (mBoundBytes.body.getD (.sort .zero)) (.succ .zero) w120 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy120 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy120 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w122 : EnvWf (envPre 122) (n+1) :=
    wfOfExtend (r := 121) (m := mBcLB) (by decide) rfl
      (.thm (envPre 121) 121 mBcLB.mtype
        (mBcLB.body.getD (.sort .zero)) w121 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA121))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody121)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w123 : EnvWf (envPre 123) (n+1) :=
    wfOfExtend (r := 122) (m := mLbRef) (by decide) rfl
      (.definition (envPre 122) 122 mLbRef.mtype
        (mLbRef.body.getD (.sort .zero)) (.succ .zero) w122 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy122 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy122 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w124 : EnvWf (envPre 124) (n+1) :=
    wfOfExtend (r := 123) (m := mCctLbPf) (by decide) rfl
      (.thm (envPre 123) 123 mCctLbPf.mtype
        (mCctLbPf.body.getD (.sort .zero)) w123 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA123))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody123)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w125 : EnvWf (envPre 125) (n+1) :=
    wfOfExtend (r := 124) (m := mBoundListBool) (by decide) rfl
      (.definition (envPre 124) 124 mBoundListBool.mtype
        (mBoundListBool.body.getD (.sort .zero)) (.succ .zero) w124 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy124 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy124 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w126 : EnvWf (envPre 126) (n+1) :=
    wfOfExtend (r := 125) (m := mNEL) (by decide) rfl
      (.indMember (envPre 125) 125 mNEL w125 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamNEL)
  have w127 : EnvWf (envPre 127) (n+1) :=
    wfOfExtend (r := 126) (m := mNelNil) (by decide) rfl
      (.indMember (envPre 126) 126 mNelNil w126 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNelNil)
  have w128 : EnvWf (envPre 128) (n+1) :=
    wfOfExtend (r := 127) (m := mNelCons) (by decide) rfl
      (.indMember (envPre 127) 127 mNelCons w127 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNelCons)
  have w129 : EnvWf (envPre 129) (n+1) :=
    wfOfExtend (r := 128) (m := recNEL) (by decide) rfl
      (.indMember (envPre 128) 128 recNEL w128 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga128) admRecNEL)
  have w130 : EnvWf (envPre 130) (n+1) :=
    wfOfExtend (r := 129) (m := mNTB) (by decide) rfl
      (.indMember (envPre 129) 129 mNTB w129 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamNTB)
  have w131 : EnvWf (envPre 131) (n+1) :=
    wfOfExtend (r := 130) (m := mNtbHere) (by decide) rfl
      (.indMember (envPre 130) 130 mNtbHere w130 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNtbHere)
  have w132 : EnvWf (envPre 132) (n+1) :=
    wfOfExtend (r := 131) (m := mNtbNext) (by decide) rfl
      (.indMember (envPre 131) 131 mNtbNext w131 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorNtbNext)
  have w133 : EnvWf (envPre 133) (n+1) :=
    wfOfExtend (r := 132) (m := recNTB) (by decide) rfl
      (.indMember (envPre 132) 132 recNTB w132 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga132) admRecNTB)
  have w134 : EnvWf (envPre 134) (n+1) :=
    wfOfExtend (r := 133) (m := mValueAt) (by decide) rfl
      (.indMember (envPre 133) 133 mValueAt w133 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamValueAt)
  have w135 : EnvWf (envPre 135) (n+1) :=
    wfOfExtend (r := 134) (m := mVaB0) (by decide) rfl
      (.indMember (envPre 134) 134 mVaB0 w134 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaB0)
  have w136 : EnvWf (envPre 136) (n+1) :=
    wfOfExtend (r := 135) (m := mVaB1) (by decide) rfl
      (.indMember (envPre 135) 135 mVaB1 w135 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaB1)
  have w137 : EnvWf (envPre 137) (n+1) :=
    wfOfExtend (r := 136) (m := mVaI64) (by decide) rfl
      (.indMember (envPre 136) 136 mVaI64 w136 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaI64)
  have w138 : EnvWf (envPre 138) (n+1) :=
    wfOfExtend (r := 137) (m := mVaStr) (by decide) rfl
      (.indMember (envPre 137) 137 mVaStr w137 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaStr)
  have w139 : EnvWf (envPre 139) (n+1) :=
    wfOfExtend (r := 138) (m := mVaY) (by decide) rfl
      (.indMember (envPre 138) 138 mVaY w138 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaY)
  have w140 : EnvWf (envPre 140) (n+1) :=
    wfOfExtend (r := 139) (m := mVaList) (by decide) rfl
      (.indMember (envPre 139) 139 mVaList w139 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaList)
  have w141 : EnvWf (envPre 141) (n+1) :=
    wfOfExtend (r := 140) (m := mVaPair) (by decide) rfl
      (.indMember (envPre 140) 140 mVaPair w140 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaPair)
  have w142 : EnvWf (envPre 142) (n+1) :=
    wfOfExtend (r := 141) (m := mVaJ) (by decide) rfl
      (.indMember (envPre 141) 141 mVaJ w141 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaJ)
  have w143 : EnvWf (envPre 143) (n+1) :=
    wfOfExtend (r := 142) (m := mVaR) (by decide) rfl
      (.indMember (envPre 142) 142 mVaR w142 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorVaR)
  have w144 : EnvWf (envPre 144) (n+1) :=
    wfOfExtend (r := 143) (m := recValueAt) (by decide) rfl
      (.indMember (envPre 143) 143 recValueAt w143 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => B.idxValueAt) admRecValueAt)
  have w145 : EnvWf (envPre 145) (n+1) :=
    wfOfExtend (r := 144) (m := mVb0) (by decide) rfl
      (.thm (envPre 144) 144 mVb0.mtype
        (mVb0.body.getD (.sort .zero)) w144 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA144))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody144)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w146 : EnvWf (envPre 146) (n+1) :=
    wfOfExtend (r := 145) (m := mVb1) (by decide) rfl
      (.thm (envPre 145) 145 mVb1.mtype
        (mVb1.body.getD (.sort .zero)) w145 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA145))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody145)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w147 : EnvWf (envPre 147) (n+1) :=
    wfOfExtend (r := 146) (m := mBytesSemi) (by decide) rfl
      (.definition (envPre 146) 146 mBytesSemi.mtype
        (mBytesSemi.body.getD (.sort .zero)) (.succ .zero) w146 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy146 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy146 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w148 : EnvWf (envPre 148) (n+1) :=
    wfOfExtend (r := 147) (m := mBytesD0) (by decide) rfl
      (.definition (envPre 147) 147 mBytesD0.mtype
        (mBytesD0.body.getD (.sort .zero)) (.succ .zero) w147 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy147 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy147 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w149 : EnvWf (envPre 149) (n+1) :=
    wfOfExtend (r := 148) (m := mBytesNat0) (by decide) rfl
      (.definition (envPre 148) 148 mBytesNat0.mtype
        (mBytesNat0.body.getD (.sort .zero)) (.succ .zero) w148 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy148 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy148 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w150 : EnvWf (envPre 150) (n+1) :=
    wfOfExtend (r := 149) (m := mBytesVLB0) (by decide) rfl
      (.definition (envPre 149) 149 mBytesVLB0.mtype
        (mBytesVLB0.body.getD (.sort .zero)) (.succ .zero) w149 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy149 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy149 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w151 : EnvWf (envPre 151) (n+1) :=
    wfOfExtend (r := 150) (m := mBytesI5) (by decide) rfl
      (.definition (envPre 150) 150 mBytesI5.mtype
        (mBytesI5.body.getD (.sort .zero)) (.succ .zero) w150 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy150 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy150 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w152 : EnvWf (envPre 152) (n+1) :=
    wfOfExtend (r := 151) (m := mBytesD5) (by decide) rfl
      (.definition (envPre 151) 151 mBytesD5.mtype
        (mBytesD5.body.getD (.sort .zero)) (.succ .zero) w151 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy151 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy151 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w153 : EnvWf (envPre 153) (n+1) :=
    wfOfExtend (r := 152) (m := mBytesNat5) (by decide) rfl
      (.definition (envPre 152) 152 mBytesNat5.mtype
        (mBytesNat5.body.getD (.sort .zero)) (.succ .zero) w152 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy152 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy152 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w154 : EnvWf (envPre 154) (n+1) :=
    wfOfExtend (r := 153) (m := mLt010) (by decide) rfl
      (.thm (envPre 153) 153 mLt010.mtype
        (mLt010.body.getD (.sort .zero)) w153 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA153))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody153)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w155 : EnvWf (envPre 155) (n+1) :=
    wfOfExtend (r := 154) (m := mNd0) (by decide) rfl
      (.thm (envPre 154) 154 mNd0.mtype
        (mNd0.body.getD (.sort .zero)) w154 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA154))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody154)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w156 : EnvWf (envPre 156) (n+1) :=
    wfOfExtend (r := 155) (m := mBc48S) (by decide) rfl
      (.thm (envPre 155) 155 mBc48S.mtype
        (mBc48S.body.getD (.sort .zero)) w155 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA155))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody155)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w157 : EnvWf (envPre 157) (n+1) :=
    wfOfExtend (r := 156) (m := mNea0) (by decide) rfl
      (.thm (envPre 156) 156 mNea0.mtype
        (mNea0.body.getD (.sort .zero)) w156 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA156))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy156 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w158 : EnvWf (envPre 158) (n+1) :=
    wfOfExtend (r := 157) (m := mBcLN0) (by decide) rfl
      (.thm (envPre 157) 157 mBcLN0.mtype
        (mBcLN0.body.getD (.sort .zero)) w157 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA157))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody157)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w159 : EnvWf (envPre 159) (n+1) :=
    wfOfExtend (r := 158) (m := mBcL0Nil) (by decide) rfl
      (.thm (envPre 158) 158 mBcL0Nil.mtype
        (mBcL0Nil.body.getD (.sort .zero)) w158 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA158))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody158)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w160 : EnvWf (envPre 160) (n+1) :=
    wfOfExtend (r := 159) (m := mNthBNilVa) (by decide) rfl
      (.thm (envPre 159) 159 mNthBNilVa.mtype
        (mNthBNilVa.body.getD (.sort .zero)) w159 rfl
        (hasTyLevelMono (Nat.zero_le (n+1)) tyType159)
        (hasTyLevelMono (Nat.succ_le_succ (Nat.zero_le n)) tyThm159)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w161 : EnvWf (envPre 161) (n+1) :=
    wfOfExtend (r := 160) (m := mVLBNil) (by decide) rfl
      (.thm (envPre 160) 160 mVLBNil.mtype
        (mVLBNil.body.getD (.sort .zero)) w160 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA160))
        (hasTyLevelMono (Nat.succ_le_succ (Nat.zero_le n)) tyThm160)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w162 : EnvWf (envPre 162) (n+1) :=
    wfOfExtend (r := 161) (m := mLt510) (by decide) rfl
      (.thm (envPre 161) 161 mLt510.mtype
        (mLt510.body.getD (.sort .zero)) w161 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA161))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody161)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w163 : EnvWf (envPre 163) (n+1) :=
    wfOfExtend (r := 162) (m := mNd5) (by decide) rfl
      (.thm (envPre 162) 162 mNd5.mtype
        (mNd5.body.getD (.sort .zero)) w162 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA162))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody162)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w164 : EnvWf (envPre 164) (n+1) :=
    wfOfExtend (r := 163) (m := mBc53S) (by decide) rfl
      (.thm (envPre 163) 163 mBc53S.mtype
        (mBc53S.body.getD (.sort .zero)) w163 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA163))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody163)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w165 : EnvWf (envPre 165) (n+1) :=
    wfOfExtend (r := 164) (m := mNea5) (by decide) rfl
      (.thm (envPre 164) 164 mNea5.mtype
        (mNea5.body.getD (.sort .zero)) w164 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA164))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy164 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w166 : EnvWf (envPre 166) (n+1) :=
    wfOfExtend (r := 165) (m := mIeaP5) (by decide) rfl
      (.thm (envPre 165) 165 mIeaP5.mtype
        (mIeaP5.body.getD (.sort .zero)) w165 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA165))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy165 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w167 : EnvWf (envPre 167) (n+1) :=
    wfOfExtend (r := 166) (m := mBcI5) (by decide) rfl
      (.thm (envPre 166) 166 mBcI5.mtype
        (mBcI5.body.getD (.sort .zero)) w166 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA166))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody166)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w168 : EnvWf (envPre 168) (n+1) :=
    wfOfExtend (r := 167) (m := mVI5) (by decide) rfl
      (.thm (envPre 167) 167 mVI5.mtype
        (mVI5.body.getD (.sort .zero)) w167 rfl
        (hasTyLevelMono (Nat.zero_le (n+1))
          (hasTy_of_inferConvAux rfl rfl infA167))
        (hasTyLevelMono (Nat.zero_le (n+1)) tyBody167)
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  exact (show envPre 168 = srcEnvG from rfl) ▸ w168

#print axioms srcEnvG_wf_of

end Rcic.Scm.SrcG
