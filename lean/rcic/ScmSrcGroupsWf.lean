import rcic.ScmSrcGroupsRecVA
import rcic.RcicAdmit
import rcic.ScmSrcGroupsKernelRfl

/-! Stage 2a: `EnvWf` for `envPre 29` — slots 0–28 of `srcMembersG`
(N / Bytes / RefT groups with recursors, the twelve byte/digest
definitions, and the DA family with its constructors).  Stops before
slot 29 because `recDA` needs the judgment's own `IndGroupAdmitted`
form, which the L-K1 findings exclude. -/

open Rcic.Declarative Rcic.Machine
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/-- One slot step: `envPre` is a `foldl` over `take`, and
`take (r+1) = take r ++ [slot r]`. -/
theorem envPre_succ {r : Nat} (hr : r < srcMembersG.length) :
    envPre (r+1) = extendEnv (envPre r)
      (srcMembersG[r]'hr).1 (srcMembersG[r]'hr).2 := by
  unfold envPre foldEnv
  rw [List.take_succ, List.getElem?_eq_getElem (h := hr)]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- Transport `EnvWf (extendEnv (envPre r) r m)` back across the
take/foldl step to `EnvWf (envPre (r+1))`. -/
private def wfOfExtend {n : Nat} {r : Nat} {m : CheckedMember}
    (hr : r < srcMembersG.length) (hm : srcMembersG[r]'hr = ⟨r, m⟩)
    (h : EnvWf (extendEnv (envPre r) r m) n) : EnvWf (envPre (r+1)) n := by
  rw [envPre_succ hr, hm]
  exact h

/-- `exprClosedAt c e`: every `bvar` in `e` is below cutoff `c` once
binding depth is accounted for — i.e. every variable is bound. -/
def exprClosedAt (c : Nat) : Expr Nat → Bool
  | .bvar i => decide (i < c)
  | .sort _ | .const _ _ | .lit _ => true
  | .app f a => exprClosedAt c f && exprClosedAt c a
  | .lam A B => exprClosedAt c A && exprClosedAt (c+1) B
  | .pi A B => exprClosedAt c A && exprClosedAt (c+1) B
  | .letE A v B => exprClosedAt c A && exprClosedAt c v && exprClosedAt (c+1) B

theorem lift_eq_of_closedAt_le {c d : Nat} {e : Expr Nat}
    (h : exprClosedAt c e = true) (hcd : c ≤ d) : lift d 1 e = e := by
  induction e generalizing c d with
  | bvar i =>
      simp only [exprClosedAt] at h
      have hi : i < c := of_decide_eq_true h
      exact if_neg (Nat.not_le.mpr (Nat.lt_of_lt_of_le hi hcd))
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f a ihf iha =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihf h.1 hcd, iha h.2 hcd]
  | lam A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1 hcd, ihB h.2 (Nat.succ_le_succ hcd)]
  | pi A B ihA ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      simp only [lift, ihA h.1 hcd, ihB h.2 (Nat.succ_le_succ hcd)]
  | letE A v B ihA ihv ihB =>
      simp only [exprClosedAt, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hv⟩, hb⟩ := h
      simp only [lift, ihA ha hcd, ihv hv hcd, ihB hb (Nat.succ_le_succ hcd)]

/-- `EnvWf`'s `hcl*` shape: a closed member is `lift`-fixed at every
cutoff. -/
private def lift_id_closed {e : Expr Nat} (h : exprClosedAt 0 e = true) :
    ∀ k, lift k 1 e = e :=
  fun k => lift_eq_of_closedAt_le h (Nat.zero_le k)

/-! Recursor-side `hidxAdm`: the Bool machine's check, kernel-verified. -/
kernel_rfl_theorem rga3 : recursorGroupAdmitted (envPre 3) 3 recN = true
kernel_rfl_theorem rga7 : recursorGroupAdmitted (envPre 7) 7 recBytes = true
kernel_rfl_theorem rga10 : recursorGroupAdmitted (envPre 10) 10 recRefT = true

private def infTy11 (n : Nat)
    (h1 : (envPre 11).members 1 = some mZero)
    (h2 : (envPre 11).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 11) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy11 (n : Nat)
    (h1 : (envPre 11).members 1 = some mZero)
    (h2 : (envPre 11).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 11) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesI.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy12 (n : Nat)
    (h1 : (envPre 12).members 1 = some mZero)
    (h2 : (envPre 12).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 12) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy12 (n : Nat)
    (h1 : (envPre 12).members 1 = some mZero)
    (h2 : (envPre 12).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 12) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesB.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy13 (n : Nat)
    (h1 : (envPre 13).members 1 = some mZero)
    (h2 : (envPre 13).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 13) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy13 (n : Nat)
    (h1 : (envPre 13).members 1 = some mZero)
    (h2 : (envPre 13).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 13) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesS.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy14 (n : Nat)
    (h1 : (envPre 14).members 1 = some mZero)
    (h2 : (envPre 14).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 14) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy14 (n : Nat)
    (h1 : (envPre 14).members 1 = some mZero)
    (h2 : (envPre 14).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 14) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesY.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy15 (n : Nat)
    (h1 : (envPre 15).members 1 = some mZero)
    (h2 : (envPre 15).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 15) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy15 (n : Nat)
    (h1 : (envPre 15).members 1 = some mZero)
    (h2 : (envPre 15).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 15) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesB0.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy16 (n : Nat)
    (h1 : (envPre 16).members 1 = some mZero)
    (h2 : (envPre 16).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 16) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy16 (n : Nat)
    (h1 : (envPre 16).members 1 = some mZero)
    (h2 : (envPre 16).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 16) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesB1.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy17 (n : Nat)
    (h1 : (envPre 17).members 1 = some mZero)
    (h2 : (envPre 17).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 17) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy17 (n : Nat)
    (h1 : (envPre 17).members 1 = some mZero)
    (h2 : (envPre 17).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 17) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mDigestI.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy18 (n : Nat)
    (h1 : (envPre 18).members 1 = some mZero)
    (h2 : (envPre 18).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 18) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy18 (n : Nat)
    (h1 : (envPre 18).members 1 = some mZero)
    (h2 : (envPre 18).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 18) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mDigestB.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy19 (n : Nat)
    (h1 : (envPre 19).members 1 = some mZero)
    (h2 : (envPre 19).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 19) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy19 (n : Nat)
    (h1 : (envPre 19).members 1 = some mZero)
    (h2 : (envPre 19).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 19) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mDigestS.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy20 (n : Nat)
    (h1 : (envPre 20).members 1 = some mZero)
    (h2 : (envPre 20).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 20) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy20 (n : Nat)
    (h1 : (envPre 20).members 1 = some mZero)
    (h2 : (envPre 20).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 20) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mDigestY.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy21 (n : Nat)
    (h1 : (envPre 21).members 1 = some mZero)
    (h2 : (envPre 21).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 21) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy21 (n : Nat)
    (h1 : (envPre 21).members 1 = some mZero)
    (h2 : (envPre 21).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 21) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mBytesLB.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

private def infTy22 (n : Nat)
    (h1 : (envPre 22).members 1 = some mZero)
    (h2 : (envPre 22).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 22) (n := n) (Γ := ([] : LCtx)) h1 h2
      (.const 4 [])).map (·.1) = some (.sort (.succ .zero)) := rfl

private def infBdy22 (n : Nat)
    (h1 : (envPre 22).members 1 = some mZero)
    (h2 : (envPre 22).members 2 = some mSucc) :
    (inferSpine2 (E := envPre 22) (n := n) (Γ := ([] : LCtx)) h1 h2
      (mDigestLB.body.getD (.sort .zero))).map (·.1) = some (.const 4 []) := rfl

def srcEnvG_prefix_wf (n : Nat) : EnvWf (envPre 29) n := by
  have w0 : EnvWf (envPre 0) n := .empty n
  have w1 : EnvWf (envPre 1) n :=
    wfOfExtend (r := 0) (m := mN) (by decide) rfl
      (.indMember (envPre 0) 0 mN w0 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamN)
  have w2 : EnvWf (envPre 2) n :=
    wfOfExtend (r := 1) (m := mZero) (by decide) rfl
      (.indMember (envPre 1) 1 mZero w1 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorZero)
  have w3 : EnvWf (envPre 3) n :=
    wfOfExtend (r := 2) (m := mSucc) (by decide) rfl
      (.indMember (envPre 2) 2 mSucc w2 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorSucc)
  have w4 : EnvWf (envPre 4) n :=
    wfOfExtend (r := 3) (m := recN) (by decide) rfl
      (.indMember (envPre 3) 3 recN w3 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga3) admRecN)
  have w5 : EnvWf (envPre 5) n :=
    wfOfExtend (r := 4) (m := mBytes) (by decide) rfl
      (.indMember (envPre 4) 4 mBytes w4 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamBytes)
  have w6 : EnvWf (envPre 6) n :=
    wfOfExtend (r := 5) (m := mBnil) (by decide) rfl
      (.indMember (envPre 5) 5 mBnil w5 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBnil)
  have w7 : EnvWf (envPre 7) n :=
    wfOfExtend (r := 6) (m := mBcons) (by decide) rfl
      (.indMember (envPre 6) 6 mBcons w6 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorBcons)
  have w8 : EnvWf (envPre 8) n :=
    wfOfExtend (r := 7) (m := recBytes) (by decide) rfl
      (.indMember (envPre 7) 7 recBytes w7 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga7) admRecBytes)
  have w9 : EnvWf (envPre 9) n :=
    wfOfExtend (r := 8) (m := mRefT) (by decide) rfl
      (.indMember (envPre 8) 8 mRefT w8 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamRefT)
  have w10 : EnvWf (envPre 10) n :=
    wfOfExtend (r := 9) (m := mMkRef) (by decide) rfl
      (.indMember (envPre 9) 9 mMkRef w9 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorMkRef)
  have w11 : EnvWf (envPre 11) n :=
    wfOfExtend (r := 10) (m := recRefT) (by decide) rfl
      (.indMember (envPre 10) 10 recRefT w10 rfl
        (Or.inr (Or.inr rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun _ => RecursorGroupIdxAdmitted.ofAdmitted rga10) admRecRefT)
  have w12 : EnvWf (envPre 12) n :=
    wfOfExtend (r := 11) (m := mBytesI) (by decide) rfl
      (.definition (envPre 11) 11 (.const 4 [])
        (mBytesI.body.getD (.sort .zero)) (.succ .zero) w11 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy11 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy11 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w13 : EnvWf (envPre 13) n :=
    wfOfExtend (r := 12) (m := mBytesB) (by decide) rfl
      (.definition (envPre 12) 12 (.const 4 [])
        (mBytesB.body.getD (.sort .zero)) (.succ .zero) w12 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy12 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy12 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w14 : EnvWf (envPre 14) n :=
    wfOfExtend (r := 13) (m := mBytesS) (by decide) rfl
      (.definition (envPre 13) 13 (.const 4 [])
        (mBytesS.body.getD (.sort .zero)) (.succ .zero) w13 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy13 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy13 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w15 : EnvWf (envPre 15) n :=
    wfOfExtend (r := 14) (m := mBytesY) (by decide) rfl
      (.definition (envPre 14) 14 (.const 4 [])
        (mBytesY.body.getD (.sort .zero)) (.succ .zero) w14 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy14 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy14 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w16 : EnvWf (envPre 16) n :=
    wfOfExtend (r := 15) (m := mBytesB0) (by decide) rfl
      (.definition (envPre 15) 15 (.const 4 [])
        (mBytesB0.body.getD (.sort .zero)) (.succ .zero) w15 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy15 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy15 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w17 : EnvWf (envPre 17) n :=
    wfOfExtend (r := 16) (m := mBytesB1) (by decide) rfl
      (.definition (envPre 16) 16 (.const 4 [])
        (mBytesB1.body.getD (.sort .zero)) (.succ .zero) w16 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy16 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy16 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w18 : EnvWf (envPre 18) n :=
    wfOfExtend (r := 17) (m := mDigestI) (by decide) rfl
      (.definition (envPre 17) 17 (.const 4 [])
        (mDigestI.body.getD (.sort .zero)) (.succ .zero) w17 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy17 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy17 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w19 : EnvWf (envPre 19) n :=
    wfOfExtend (r := 18) (m := mDigestB) (by decide) rfl
      (.definition (envPre 18) 18 (.const 4 [])
        (mDigestB.body.getD (.sort .zero)) (.succ .zero) w18 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy18 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy18 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w20 : EnvWf (envPre 20) n :=
    wfOfExtend (r := 19) (m := mDigestS) (by decide) rfl
      (.definition (envPre 19) 19 (.const 4 [])
        (mDigestS.body.getD (.sort .zero)) (.succ .zero) w19 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy19 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy19 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w21 : EnvWf (envPre 21) n :=
    wfOfExtend (r := 20) (m := mDigestY) (by decide) rfl
      (.definition (envPre 20) 20 (.const 4 [])
        (mDigestY.body.getD (.sort .zero)) (.succ .zero) w20 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy20 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy20 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w22 : EnvWf (envPre 22) n :=
    wfOfExtend (r := 21) (m := mBytesLB) (by decide) rfl
      (.definition (envPre 21) 21 (.const 4 [])
        (mBytesLB.body.getD (.sort .zero)) (.succ .zero) w21 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy21 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy21 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w23 : EnvWf (envPre 23) n :=
    wfOfExtend (r := 22) (m := mDigestLB) (by decide) rfl
      (.definition (envPre 22) 22 (.const 4 [])
        (mDigestLB.body.getD (.sort .zero)) (.succ .zero) w22 rfl
        (hasTy_of_inferSpine2_eq rfl rfl (infTy22 n rfl rfl))
        (hasTy_of_inferSpine2_eq rfl rfl (infBdy22 n rfl rfl))
        (lift_id_closed (by decide)) (lift_id_closed (by decide)))
  have w24 : EnvWf (envPre 24) n :=
    wfOfExtend (r := 23) (m := mDA) (by decide) rfl
      (.indMember (envPre 23) 23 mDA w23 rfl
        (Or.inl rfl) rfl
        (lift_id_closed (by decide)) (fun _ => rfl)
        rfl rfl rfl (fun h => absurd h (by decide)) admFamDA)
  have w25 : EnvWf (envPre 25) n :=
    wfOfExtend (r := 24) (m := mDaI) (by decide) rfl
      (.indMember (envPre 24) 24 mDaI w24 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDaI)
  have w26 : EnvWf (envPre 26) n :=
    wfOfExtend (r := 25) (m := mDaB) (by decide) rfl
      (.indMember (envPre 25) 25 mDaB w25 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDaB)
  have w27 : EnvWf (envPre 27) n :=
    wfOfExtend (r := 26) (m := mDaS) (by decide) rfl
      (.indMember (envPre 26) 26 mDaS w26 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDaS)
  have w28 : EnvWf (envPre 28) n :=
    wfOfExtend (r := 27) (m := mDaY) (by decide) rfl
      (.indMember (envPre 27) 27 mDaY w27 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDaY)
  have w29 : EnvWf (envPre 29) n :=
    wfOfExtend (r := 28) (m := mDaLB) (by decide) rfl
      (.indMember (envPre 28) 28 mDaLB w28 rfl
        (Or.inr (Or.inl rfl)) rfl
        (lift_id_closed (by decide)) (fun h => absurd h (by decide))
        rfl rfl rfl (fun h => absurd h (by decide)) admCtorDaLB)
  exact w29

#print axioms Rcic.Scm.SrcG.srcEnvG_prefix_wf

end Rcic.Scm.SrcG
